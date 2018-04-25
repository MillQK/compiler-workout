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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
  (match insn with
  | BINOP op -> let y::x::stack' = stack in eval env (cstack, Expr.to_func op x y :: stack', c) prg'
  | READ     -> let z::i'        = i     in eval env (cstack, z::stack, (st, i', o)) prg'
  | WRITE    -> let z::stack'    = stack in eval env (cstack, stack', (st, i, o @ [z])) prg'
  | CONST i  -> eval env (cstack, i::stack, c) prg'
  | LD x     -> eval env (cstack, (State.eval st x) :: stack, c) prg'
  | ST x     -> let z::stack'    = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
  | LABEL _  -> eval env conf prg'
  | JMP l    -> eval env conf (env#labeled l)
  | CJMP (cond, l) ->
    let z::stack' = stack in
    let is_jump = match cond with
    | "nz" -> z <> 0
    | "z" -> z == 0
    in eval env (cstack, stack', c) (if is_jump then (env#labeled l) else prg')
  | BEGIN (_, args, locals) ->
    let rec fun_init_state state = function
      | arg::args, el::stk ->
        let n_state, n_stack = fun_init_state state (args, stk) in
        State.update arg el n_state, n_stack
      | [], stk -> state, stk
    in
    let stt, stk = fun_init_state (State.enter st (args @ locals)) (args, stack) in
    eval env (cstack, stk, (stt, i, o)) prg'
  | CALL (f_name, _, _) -> (
    eval env ((prg', st)::cstack, stack, c) (env#labeled f_name)
    )
  | END | RET _ -> (
    match cstack with
    | (p, stt)::cstack' -> eval env (cstack', stack, (State.leave st stt, i, o)) p
    | [] -> conf
    )
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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let label_gen = object
  val mutable label_num = 0
  method next_label =
    label_num <- (label_num + 1);
    "l" ^ (string_of_int label_num)
end

let rec compile_expr = function
| Expr.Var   x          -> [LD x]
| Expr.Const n          -> [CONST n]
| Expr.Binop (op, x, y) -> (compile_expr x) @ (compile_expr y) @ [BINOP op]
| Expr.Call (f_name, args) -> List.concat (List.map compile_expr args) @ [CALL (f_name, List.length args, false)]

let rec compile_stmt = function
| Stmt.Seq (s1, s2)  -> (compile_stmt s1) @ (compile_stmt s2)
| Stmt.Read x        -> [READ; ST x]
| Stmt.Write e       -> (compile_expr e) @ [WRITE]
| Stmt.Assign (x, e) -> (compile_expr e) @ [ST x]
| Stmt.Skip -> []
| Stmt.If (c_expr, t_stmt, f_stmt) -> (
  let else_label = label_gen#next_label in 
  let end_label = label_gen#next_label in
  let t_stmt_comp = compile_stmt t_stmt in
  let f_stmt_comp = compile_stmt f_stmt in
  (compile_expr c_expr @ [CJMP ("z", else_label)] @ t_stmt_comp @ [JMP end_label] @ [LABEL else_label] @ f_stmt_comp @ [LABEL end_label])
)
| Stmt.While (c_expr, w_stmt) -> (
  let while_body_label = label_gen#next_label in
  let end_label = label_gen#next_label in
  let w_stmt_comp = compile_stmt w_stmt in
  ([JMP end_label] @ [LABEL while_body_label] @ w_stmt_comp @ [LABEL end_label] @ compile_expr c_expr @ [CJMP ("nz", while_body_label)])
)
| Stmt.Repeat (r_stmt, c_expr) -> (
  let repeat_body_label = label_gen#next_label in
  let r_stmt_comp = compile_stmt r_stmt in
  ([LABEL repeat_body_label] @ r_stmt_comp @ compile_expr c_expr @ [CJMP ("z", repeat_body_label)])
)
| Stmt.Call (f_name, args) -> (
  let list_compiled_args = List.map compile_expr (List.rev args) in
  let compiled_args = List.concat list_compiled_args in
  compiled_args @ [CALL (f_name, List.length args, true)]
)
| Stmt.Return m_v -> (match m_v with Some v -> (compile_expr v) | None -> []) @ [RET (m_v <> None)]

let rec compile_def (f_name, (f_args, f_locals, f_body)) = 
[LABEL (f_name); BEGIN (f_name, f_args, f_locals)] @ compile_stmt f_body @ [END]

let rec compile (defs, p) = compile_stmt p @ [END] @ List.concat (List.map compile_def defs)

