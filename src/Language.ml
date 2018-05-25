(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
        let init_list n f =
      let rec init i n f =
        if i >= n then []
        else (f i) :: (init (i + 1) n f)
      in init 0 n f
    let update_array  a i x = init_list   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let int_to_bool value = 
      if value == 0 then false else true
    let bool_to_int value = 
      if value then 1 else 0

    let binop operation left_operand right_operand = 
      match operation with
      | "+"   -> left_operand + right_operand
      | "-"   -> left_operand - right_operand
      | "*"   -> left_operand * right_operand
      | "/"   -> left_operand / right_operand
      | "%"   -> left_operand mod right_operand
      | "&&"  -> bool_to_int (int_to_bool left_operand && int_to_bool right_operand)
      | "!!"  -> bool_to_int (int_to_bool left_operand || int_to_bool right_operand)
      | "<" -> bool_to_int (left_operand < right_operand)
      | "<="  -> bool_to_int (left_operand <= right_operand)
      | ">" -> bool_to_int (left_operand > right_operand)
      | ">="  -> bool_to_int (left_operand >= right_operand)
      | "=="  -> bool_to_int (left_operand == right_operand)
      | "!="  -> bool_to_int (left_operand != right_operand)
      | _ -> failwith("Undefined operator!")


    let rec eval env ((st, i, o, r) as conf) expr =
      match expr with
      | Const const -> (st, i, o, Some (Value.of_int const))
      | Array elements -> 
        let (st, i, o, vs) as conf = eval_list env conf elements in 
        (st, i, o, Some (Value.of_array vs))
      | String s -> (st, i, o, Some (Value.of_string s))
      | Sexp (t, elements) ->
        let (st, i, o, vs) = eval_list env conf elements in 
        (st, i, o, Some (Value.sexp t vs))
      | Var variable -> 
        let value = State.eval st variable in
        (st, i, o, Some value)
      | Binop (operation, left, right) ->
        let (st', i', o', Some l) as conf' = eval env conf left in
        let (st', i', o', Some r) = eval env conf' right in
        let value = binop operation (Value.to_int l) (Value.to_int r) in 
        (st', i', o', Some (Value.of_int value))
      | Elem (x, i) -> 
        let (_, _, _, Some vx) as conf = eval env conf x in
        let (_, _, _, Some vi) as conf = eval env conf i in 
        env#definition env ".elem" [vx; vi] conf
      | Length expr -> 
        let (st, i, o, Some v) as conf = eval env conf expr in 
        env#definition env ".length" [v] conf
      | Call (name, args) ->
        let rec evalArgs env conf args =
          match args with
          | expr::args' ->
            let (st', i', o', Some eval_arg) as conf' = eval env conf expr in
            let eval_args', conf' = evalArgs env conf' args' in 
            eval_arg::eval_args',   conf'
          |[] -> [], conf  
        in
        let eval_args, conf' = evalArgs env conf args in
        env#definition env name eval_args conf'
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
  let mapoperation operations = List.map (fun operation -> ostap($(operation)), (fun left right -> Binop (operation, left, right))) operations

    ostap (
      parse: 
        !(Ostap.Util.expr
          (fun x -> x)
          [|
            `Lefta, mapoperation ["!!"];
            `Lefta, mapoperation ["&&"];
            `Nona,  mapoperation ["=="; "!=";">="; ">"; "<="; "<"];
            `Lefta, mapoperation ["+"; "-"];
            `Lefta, mapoperation ["*"; "/"; "%"];
          |]
          primary
        );
      primary: 
        e:expr action:(
          -"[" i:parse -"]" {`Elem i} 
          | -"." %"length" {`Len}
        ) * {List.fold_left (fun x -> function `Elem i -> Elem (x, i) | `Len -> Length x) e action};
      expr:  
        x:IDENT "(" args:!(Util.list0)[parse] ")" {Call (x, args)}
        | variable:IDENT {Var variable} 
        | const:DECIMAL {Const const} 
        | s:STRING {String (String.sub s 1 (String.length s - 2))}
        | c:CHAR {Const (Char.code c)}
        | "`" t:IDENT args:(-"(" !(Util.list)[parse] -")")? {Sexp (t, match args with None -> [] | Some args -> args)}
        | -"[" elements:!(Util.list0)[parse] -"]" {Array elements}
        | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse:  
            "_" {Wildcard}
            | "`" t:IDENT args:(-"(" !(Ostap.Util.list)[parse] -")")? {Sexp (t, match args with None -> [] | Some args -> args)}
            | x:IDENT {Ident x}
        )
        
        let vars p = 
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

        let rec eval env conf k stmt =
      let romb stmt k =
        if k = Skip then stmt
        else Seq (stmt, k) in
      match conf, stmt with
      | (st, input, output, r) , Assign (variable, indexs, expr) -> 
        let (st', i', o', inds) = Expr.eval_list env conf indexs in
        let (st', i', o', Some value) = Expr.eval env conf expr in
        eval env (update st' variable value inds, i', o', None) Skip k
      | conf, Seq (left_stmt, right_stmt) ->
        eval env conf (romb right_stmt k) left_stmt
      | conf, Skip -> 
        if k = Skip then conf
        else eval env conf Skip k
      | (st, input, output, r), If (expr, th, el) ->
        let (st', i', o', Some value) as conf' = Expr.eval env conf expr in
        let if_answer value = if Value.to_int value == 0 then el else th in
        eval env conf' k (if_answer value)
      | conf, While (expr, while_stmt) ->
        let (st', i', o', Some value) as conf' = Expr.eval env conf expr in
        if Value.to_int value == 0 then eval env conf' Skip k
        else eval env conf' (romb stmt k) while_stmt
      | conf, Repeat (expr, repeat_stmt) ->
        eval env conf (romb (While(Expr.Binop("==",expr, Expr.Const 0), repeat_stmt)) k) repeat_stmt
      | (st, input, output, r), Call (name, args) ->
        let rec evalArgs env conf args =
          match args with
          | expr::args' ->
            let (st', i', o', Some eval_arg) = Expr.eval env conf expr in
            let eval_args', conf' = evalArgs env (st', i', o', Some eval_arg) args' in 
            eval_arg::eval_args', conf'
          |[] -> [], conf  in
          let eval_args, conf' = evalArgs env conf args in
          let conf'' = env#definition env name eval_args conf' in
          eval env conf'' Skip k
      | (st, input, output, r), Return expr -> (
        match expr with
        | None -> (st, input, output, None)
        | Some expr -> Expr.eval env conf expr
      )
      | (st, input, output, r), Case (expr, pats) ->
     let (st', i', o', Some v) as conf = Expr.eval env conf expr in 
     let rec match_pat (p : Pattern.t) (value : Value.t) state = 
       (match p, value with
         Wildcard, _ -> Some state
       | Ident x, value -> Some (State.bind x value state)
       | Sexp (t, ep), Sexp (t', ev) when ((t = t') && (List.length ep = List.length ev)) -> 
         (List.fold_left2 (fun acc curp curs -> match acc with (Some s) -> (match_pat curp curs s) | None -> None) (Some state) ep ev)
       | _, _ -> None) in
     let rec check_pat ps = 
       (match ps with
         [] -> eval env conf Skip k
       | (p, act)::tl -> 
         let match_res = match_pat p v State.undefined in
         (match match_res with
           None -> check_pat tl
         | Some s -> 
           let st'' = State.push st' s (Pattern.vars p) in
           eval env (st'', i', o', None) k (Seq (act, Leave)))) in
     check_pat pats
      | (st, input, output, r), Leave -> eval env (State.drop st, input, output, r) Skip k
      | _, _ -> failwith("Undefined statement!")
                                                        
    (* Statement parser *)
    ostap (
     
      parse: 
      seq | stmt;
  
      stmt:
          assign | skip | repeat_stmt | while_stmt | if_stmt | for_stmt | call | ret | case;

      assign: 
        variable:IDENT indexs:(-"[" !(Expr.parse) -"]")* -":=" expr:!(Expr.parse) {Assign (variable, indexs, expr)};
      skip: 
        %"skip" {Skip};
      if_stmt: 
        %"if" expr:!(Expr.parse) %"then"
        if_true:parse 
        if_false:else_stmt %"fi" {If (expr, if_true, if_false)};
      else_stmt:  
          %"else" if_false:parse {if_false} 
          | %"elif" expr:!(Expr.parse) %"then"
            if_true:parse 
            if_false:else_stmt {If (expr, if_true, if_false)}
          | "" {Skip};
      while_stmt:
        %"while" expr:!(Expr.parse) %"do"
        while_body:parse
        %"od" {While (expr, while_body)};
      repeat_stmt:
        %"repeat" 
        repeat_body:parse 
        %"until" expr:!(Expr.parse) {Repeat (expr, repeat_body)};
      for_stmt:
        %"for" init:parse -"," expr:!(Expr.parse) -"," loop:parse %"do"
        for_body:parse
        %"od" { Seq (init, While(expr, Seq (for_body, loop))) };
      call: 
        x:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)};
      ret: 
        %"return" expr:!(Expr.parse)? { Return expr };
      seq: 
        left_stmt:stmt -";" right_stmt:parse {Seq (left_stmt, right_stmt)};
      case: 
        %"case" expr:!(Expr.parse) %"of" patterns:!(Ostap.Util.listBy)[ostap ("|")][pattern] %"esac" {Case (expr, patterns)};
      pattern: 
        p:!(Pattern.parse) "->" action:!(parse) {p, action}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
