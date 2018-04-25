(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op) 
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)                                                       
    let rec eval env ((st, i, o, r) as conf) expr =
      match expr with
      | Const n -> (st, i, o, Some n)
      | Var x -> (st, i, o, Some (State.eval st x))
      | Binop (op, x, y) ->
        let (_, _, _, Some a) as a_conf = eval env conf x in
        let (n_st, n_i, n_o, Some b) as b_conf = eval env a_conf y in
        (n_st, n_i, n_o, Some (to_func op a b))
      | Call (f_name, args) ->
        let v_args, f_conf =
          List.fold_left (fun (acc, conf) e -> let (_, _, _, Some v) as conf = eval env conf e in v::acc, conf) ([], conf) args
        in
        env#definition env f_name (List.rev v_args) f_conf  
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
              (fun x -> x)
	            (Array.map (fun (a, s) -> a, 
              List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
              `Lefta, ["!!"];
              `Lefta, ["&&"];
              `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
              `Lefta, ["+" ; "-"];
              `Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     primary);
      
      primary:
        f_name:IDENT -"(" args:!(Util.list0)[parse] -")" { Call (f_name, args) }
      |  n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")" 
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let seq x = function Skip -> x | y -> Seq(x, y) in
      match stmt with
      | Read    x       -> (match i with z::i' -> (eval env (State.update x z st, i', o, r) Skip k) | _ -> failwith "Unexpected end of input")
      | Write   e       -> eval env (let (st, i, o, Some v) = Expr.eval env conf e in (st, i, o @ [v], r)) Skip k
      | Assign (x, e)   -> eval env (let (st, i, o, Some v) = Expr.eval env conf e in (State.update x v st, i, o, r)) Skip k
      | Seq    (s1, s2) -> eval env conf (seq s2 k) s1
      | Skip            -> (match k with Skip -> conf | _ -> eval env conf Skip k)
      | If (expr, t_stmt, f_stmt) -> let (_, _, _, Some v) = Expr.eval env conf expr in eval env conf k (if v <> 0 then t_stmt else f_stmt)
      | While (expr, w_stmt) -> let (_, _, _, Some v) = Expr.eval env conf expr in
                                if v <> 0
                                then eval env conf (seq stmt k) w_stmt
                                else eval env conf Skip k
      | Repeat (r_stmt, expr) -> eval env conf (seq (While (Expr.Binop ("==", expr, Expr.Const 0), r_stmt)) k) r_stmt
      | Return expr -> (match expr with None -> (st, i, o, None) | Some e -> Expr.eval env conf e)
      | Call (name, expr_args) -> eval env (Expr.eval env conf (Expr.Call (name, expr_args))) Skip k
         
    let rec parse_elif_else elif_part else_part =
      match elif_part with 
      | [] -> (
        match else_part with
        | None -> Skip
        | Some else_stmt -> else_stmt
      )
      | (expr, elif_stmt)::remain_elif -> If (expr, elif_stmt, parse_elif_else remain_elif else_part)                         

    
    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;

      function_args: head:!(Expr.parse) tail:((-"," !(Expr.parse))* ) { head :: tail } | empty { [] };

      stmt:
        "read" "(" x:IDENT ")"          {Read x}
      | "write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
      | %"skip"                          {Skip}
      | %"if" e:!(Expr.parse) %"then" t_stmt:parse
        elif_part:(%"elif" !(Expr.parse) %"then" parse)*
        else_part:(%"else" parse)?
        %"fi" {If (e, t_stmt, parse_elif_else elif_part else_part)}
      | %"while" e:!(Expr.parse) %"do" w_stmt:!(parse) %"od" {While (e, w_stmt)}
      | %"repeat" r_stmt:!(parse) %"until" e:!(Expr.parse) {Repeat (r_stmt, e)}
      | %"for" init_stmt:!(parse) "," e:!(Expr.parse) "," update_stmt:!(parse) 
        %"do" loop_stmt:!(parse) %"od" {Seq (init_stmt, While (e, Seq (loop_stmt, update_stmt)))}
      | name:IDENT "(" args:function_args ")" { Call (name, args) }
      | %"return" expr:!(Expr.parse)? {Return expr}
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
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
