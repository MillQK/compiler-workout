open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
  (match insn with
  | BINOP op -> let y::x::stack' = stack in eval env (cstack, (Value.of_int @@ Expr.to_func op (Value.to_int x) (Value.to_int y)) :: stack', c) prg'
  | CONST i  -> eval env (cstack, (Value.of_int i)::stack, c) prg'
  | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) prg'
  | SEXP (tag, count) -> let exprs, rest = split count stack in eval env (cstack, (Value.sexp tag (List.rev exprs)) :: rest, c) prg'
  | LD x     -> eval env (cstack, (State.eval st x) :: stack, c) prg'
  | ST x     -> let z::stack'    = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
  | STA (x, n) -> 
    let v::ind, stack' = split (n + 1) stack in 
    eval env (cstack, stack', (Language.Stmt.update st x v (List.rev ind), i, o)) prg'
  | LABEL _  -> eval env conf prg'
  | JMP l    -> eval env conf (env#labeled l)
  | CJMP (cond, l) ->
    let z::stack' = stack in
    let is_jump = match cond with
    | "nz" -> Value.to_int z <> 0
    | "z" -> Value.to_int z == 0
    in eval env (cstack, stack', c) (if is_jump then (env#labeled l) else prg')
  | BEGIN (_, args, local_vars) ->
    let init_val = fun x ((v :: stack), st) -> (stack, State.update x v st) in
    let (stack', st') = List.fold_right init_val args (stack, State.enter st (args @ local_vars)) in
    eval env (cstack, stack', (st', i, o)) prg'
  | CALL (f_name, n, p) -> (
    if env#is_label f_name
    then eval env ((prg', st)::cstack, stack, c) (env#labeled f_name) 
    else eval env (env#builtin conf f_name n p) prg'
    )
  | END | RET _ -> (
    match cstack with
    | (p, stt)::cstack' -> eval env (cstack', stack, (State.leave st stt, i, o)) p
    | [] -> conf
    )
  | DROP -> eval env (cstack, List.tl stack, c) prg'
  | DUP -> let hd::_ = stack in eval env (cstack, hd::stack, c) prg'
  | SWAP -> let x::y::rest = stack in eval env (cstack, y::x::rest, c) prg'
  | TAG s -> 
    let sexp::tl = stack in 
    let res = if s = Value.tag_of sexp then 1 else 0 in 
    eval env (cstack, (Value.of_int res)::tl, c) prg'
  | ENTER es -> 
    let vals, rest = split (List.length es) stack in
    let st' = List.fold_left2 (fun acc_st e var -> State.bind var e acc_st) State.undefined vals es in 
    eval env (cstack, rest, (State.push st st' es, i, o)) prg'
  | LEAVE -> eval env (cstack, stack, (State.drop st, i, o)) prg'
  )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (f, List.length args, p)]
  and pattern lfalse patt = 
    (
      let rec comp patt = 
      (
        match patt with
        | Stmt.Pattern.Wildcard -> [DROP]
        | Stmt.Pattern.Ident x -> [DROP]
        | Stmt.Pattern.Sexp (tag, patts) -> 
        let res, _ = (List.fold_left (fun (acc, pos) pat -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ (comp pat)), pos + 1) ([], 0) patts) in
        [DUP; TAG tag; CJMP ("z", lfalse)] @ res
      ) in comp patt
    )
  and bindings p = 
    let rec bind patt =
    (
      match patt with
      | Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident _ -> [SWAP]
      | Stmt.Pattern.Sexp (_, xs) ->
        let res, _ = List.fold_left (fun (acc, pos) cur_patt -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind cur_patt, pos + 1)) ([], 0) xs 
        in res @ [DROP]
      
    ) in bind p @ [ENTER (Stmt.Pattern.vars p)]

  and expr e = 
  (
    match e with
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.String s -> [STRING s]
    | Expr.Binop (op, x, y) -> (expr x) @ (expr y) @ [BINOP op]
    | Expr.Call (f_name, args) -> call (label f_name) args false
    | Expr.Array xs -> call ".array" xs false 
    | Expr.Elem (ar, idx) -> call ".elem" [ar; idx] false
    | Expr.Length e -> call ".length" [e] false
    | Expr.Sexp (tag, exs) -> let compiled_exprs = List.fold_left (fun acc ex -> acc @ (expr ex)) [] exs in compiled_exprs @ [SEXP (tag, List.length exs)]
  )
  in
  let rec compile_stmt l env stmt =  
  (
    match stmt with
    | Stmt.Seq (s1, s2)  -> 
      let env, _, c_s1 = compile_stmt l env s1 in
      let env, _, c_s2 = compile_stmt l env s2 in
      env, false, c_s1 @ c_s2
    | Stmt.Assign (x, [], e) -> env, false, (expr e) @ [ST x]
    | Stmt.Assign (x, idxs, e) -> env, false, List.flatten (List.map expr (idxs @ [e])) @ [STA (x, List.length idxs)]
    | Stmt.Skip -> env, false, []
    | Stmt.If (c_expr, t_stmt, f_stmt) -> (
      let else_label, env = env#get_label in 
      let end_label, env = env#get_label in
      let env, _, t_stmt_comp = compile_stmt l env t_stmt in
      let env, _, f_stmt_comp = compile_stmt l env f_stmt in
      env, false, (expr c_expr @ [CJMP ("z", else_label)] @ t_stmt_comp @ [JMP end_label] @ [LABEL else_label] @ f_stmt_comp @ [LABEL end_label])
    )
    | Stmt.While (c_expr, w_stmt) -> (
      let while_body_label, env = env#get_label in
      let end_label, env = env#get_label in
      let env, _, w_stmt_comp = compile_stmt l env w_stmt in
      env, false, ([JMP end_label] @ [LABEL while_body_label] @ w_stmt_comp @ [LABEL end_label] @ expr c_expr @ [CJMP ("nz", while_body_label)])
    )
    | Stmt.Repeat (r_stmt, c_expr) -> (
      let repeat_body_label, env = env#get_label in
      let env, _, r_stmt_comp = compile_stmt l env r_stmt in
      env, false, ([LABEL repeat_body_label] @ r_stmt_comp @ expr c_expr @ [CJMP ("z", repeat_body_label)])
    )
    | Stmt.Call (f_name, args) -> env, false, call (label f_name) args true
    | Stmt.Return m_v -> env, false, (match m_v with Some v -> (expr v) | None -> []) @ [RET (m_v <> None)]
    | Stmt.Case (ex, patts) -> 
      let rec compile_pattern ps env lbl isFirst lend = 
        (
        match ps with
        | [] -> env, []
        | (p, act)::tl -> 
          let env, _, body = compile_stmt l env act in 
          let lfalse, env = env#get_label
          and start = if isFirst then [] else [LABEL lbl] in
          let env, code = compile_pattern tl env lfalse false lend in
          env, start @ (pattern lfalse p) @ bindings p @ body @ [LEAVE; JMP lend] @ code
        ) in
      let lend, env = env#get_label in
      let env, code = compile_pattern patts env "" true lend in
      env, false, expr ex @ code @ [LABEL lend]
    | Stmt.Leave -> env, false, [LEAVE]
  )
  in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 
