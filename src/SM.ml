open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env ((stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
  (match insn with
  | BINOP op -> let y::x::stack' = stack in eval env (Expr.to_func op x y :: stack', c) prg'
  | READ     -> let z::i'        = i     in eval env (z::stack, (st, i', o)) prg'
  | WRITE    -> let z::stack'    = stack in eval env (stack', (st, i, o @ [z])) prg'
  | CONST i  -> eval env (i::stack, c) prg'
  | LD x     -> eval env (st x :: stack, c) prg'
  | ST x     -> let z::stack'    = stack in eval env (stack', (Expr.update x z st, i, o)) prg'
  | LABEL _  -> eval env conf prg'
  | JMP l    -> eval env conf (env#labeled l)
  | CJMP (cond, l) ->
    let z::stack' = stack in
    let is_jump = match cond with
    | "nz" -> z <> 0
    | "z" -> z == 0
    in eval env (stack', c) (if is_jump then (env#labeled l) else prg')
  )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let label_gen = object
  val mutable label_num = 0
  method next_label =
    label_num <- (label_num + 1);
    "l" ^ (string_of_int label_num)
end

let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
  | Stmt.Skip -> []
  | Stmt.If (c_expr, t_stmt, f_stmt) -> (
    let else_label = label_gen#next_label in 
    let end_label = label_gen#next_label in
    let t_stmt_comp = compile t_stmt in
    let f_stmt_comp = compile f_stmt in
    (expr c_expr @ [CJMP ("z", else_label)] @ t_stmt_comp @ [JMP end_label] @ [LABEL else_label] @ f_stmt_comp @ [LABEL end_label])
  )
  | Stmt.While (c_expr, w_stmt) -> (
    let while_body_label = label_gen#next_label in
    let end_label = label_gen#next_label in
    let w_stmt_comp = compile w_stmt in
    ([JMP end_label] @ [LABEL while_body_label] @ w_stmt_comp @ [LABEL end_label] @ expr c_expr @ [CJMP ("nz", while_body_label)])
  )
  | Stmt.Repeat (r_stmt, c_expr) -> (
    let repeat_body_label = label_gen#next_label in
    let r_stmt_comp = compile r_stmt in
    ([LABEL repeat_body_label] @ r_stmt_comp @ expr c_expr @ [CJMP ("z", repeat_body_label)])
  )