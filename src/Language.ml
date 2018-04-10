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
    let empty = {g = (fun x -> failwith (Printf.sprintf "Undefined variable %s" x)); 
                 l = (fun x -> failwith (Printf.sprintf "Undefined variable %s" x)); scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = 
      let update_state st y = if x = y then v else st y in
      if (List.mem x s.scope)
      then {s with l = update_state s.l}
      else {s with g = update_state s.g}
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if (List.mem x s.scope) then s.l x else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {g = st.g; l = (fun x -> failwith (Printf.sprintf "Undefined variable %s" x)); scope = xs}

    (* Drops a scope *)
    let leave st st' = {g = st.g; l = st'.l; scope = st'.scope}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
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

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let rec eval st expr = 
    match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

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
        n:DECIMAL {Const n}
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)

    let rec eval env ((st, i, o) as conf) stmt =
      match stmt with
      | Read    x       -> (match i with z::i' -> (State.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write   e       -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (State.update x (Expr.eval st e) st, i, o)
      | Seq    (s1, s2) -> eval env (eval env conf s1) s2
      | Skip            -> conf
      | If (expr, t_stmt, f_stmt) -> if (Expr.eval st expr) <> 0 then eval env conf t_stmt else eval env conf f_stmt
      | While (expr, w_stmt) -> (
        let rec eval_while_loop ((loop_st, _, _) as loop_conf) = if (Expr.eval loop_st expr) <> 0 then eval_while_loop (eval env loop_conf w_stmt) else loop_conf
        in eval_while_loop conf
      )
      | Repeat (r_stmt, expr) -> (
        let rec eval_repeat_loop ((loop_st, _, _) as loop_conf) = 
          let ((next_st, _, _) as next_conf) = eval env loop_conf r_stmt in
          if (Expr.eval next_st expr) == 0 then eval_repeat_loop next_conf else next_conf
        in eval_repeat_loop conf
      )
      | Call (name, expr_args) -> (
        let rec zip = function
        | x::xs, y::ys -> (x, y) :: zip (xs, ys)
        | [], [] -> []
        | _ -> failwith "Arguments count not equal in function call and definition"
        in
        let args, locals, body = env#definition name in
        let fun_enter_state = State.enter st (args @ locals) in
        let update_state_args up_st (arg, e) = State.update arg (Expr.eval st e) up_st in
        let fun_init_state = List.fold_left update_state_args fun_enter_state (zip (args, expr_args)) in
        let fun_last_state, i, o = eval env (fun_init_state, i, o) body in
        State.leave fun_last_state st, i, o
      )

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
      | %"if" e:!(Expr.parse) %"then" t_stmt:!(parse)
        elif_part:(%"elif" !(Expr.parse) %"then" parse)*
        else_part:(%"else" parse)?
        %"fi" {If (e, t_stmt, parse_elif_else elif_part else_part)}
      | %"while" e:!(Expr.parse) %"do" w_stmt:!(parse) %"od" {While (e, w_stmt)}
      | %"repeat" r_stmt:!(parse) %"until" e:!(Expr.parse) {Repeat (r_stmt, e)}
      | %"for" init_stmt:!(parse) "," e:!(Expr.parse) "," update_stmt:!(parse) 
        %"do" loop_stmt:!(parse) %"od" {Seq (init_stmt, While (e, Seq (loop_stmt, update_stmt)))}
      | name:IDENT "(" args:function_args ")" { Call (name, args) }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: %"fun" name:IDENT "(" args:((head:IDENT tail:((-"," IDENT)* ) { head :: tail }) | empty { [] }) ")" 
      vars:(-(%"local") (head:IDENT tail:((-"," IDENT)* ) { head :: tail }) | empty { [] })
      "{" body:!(Stmt.parse) "}" { name, (args, vars, body) }
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
  let funs = List.fold_left (fun acc_map (fun_name, fun_def) -> M.add fun_name fun_def acc_map) M.empty defs in
  let (_, _, output) = Stmt.eval (object method definition f = M.find f funs end) (State.empty, i, []) body in
  output
                                   
(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
