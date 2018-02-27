open GT       
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

let int_of_bool b = if b then 1 else 0
let bool_of_int i = i != 0

(* Binop interpreter
    val eval_binop : string -> int -> int -> int
*)

let rec eval_binop op v1 v2 = 
  match op with
  | "+" -> v1 + v2
  | "-" -> v1 - v2
  | "*" -> v1 * v2
  | "/" -> v1 / v2
  | "%" -> v1 mod v2
  | "==" -> int_of_bool (v1 == v2) 
  | "!=" -> int_of_bool (v1 != v2) 
  | "<=" -> int_of_bool (v1 <= v2) 
  | "<" ->  int_of_bool (v1 < v2) 
  | ">=" -> int_of_bool (v1 >= v2) 
  | ">" -> int_of_bool (v1 > v2) 
  | "!!" -> int_of_bool ((bool_of_int v1) || (bool_of_int v2)) 
  | "&&" -> int_of_bool ((bool_of_int v1) && (bool_of_int v2)) 
  | _ -> failwith (Printf.sprintf "Undefined operator %s" op)

(* Instruction interpreter
    val eval_insn : config -> insn -> config
*)

let rec eval_insn conf inst =
  match conf, inst with
  | (y::x::stk, st_cf), BINOP op -> ((eval_binop op x y)::stk, st_cf)
  | (stk, st_cf), CONST c -> (c::stk, st_cf)
  | (stk, (st, el::i, o)), READ -> (el::stk, (st, i, o))
  | (el::stk, (st, i, o)), WRITE -> (stk, (st, i, o@[el]))
  | (stk, (st, i, o)), LD var -> ((st var)::stk, (st, i, o))
  | (el::stk, (st, i, o)), ST var -> (stk, (Syntax.Expr.update var el st, i, o))

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval conf prog =
  match prog with
  | [] -> conf
  | (ins::prgm) -> eval (eval_insn conf ins) prgm

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* 
   val compile_expr : Syntax.Expr.t -> prg
 *)

let rec compile_expr expr =
  match expr with
  | Syntax.Expr.Const c -> [CONST c]
  | Syntax.Expr.Var v -> [LD v]
  | Syntax.Expr.Binop (op, exp1, exp2) -> compile_expr exp1 @ compile_expr exp2 @ [BINOP op]


(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile stmt =
  match stmt with
  | Syntax.Stmt.Read var -> [READ; ST var]
  | Syntax.Stmt.Write expr -> compile_expr expr @ [WRITE]
  | Syntax.Stmt.Assign (var, expr) -> compile_expr expr @ [ST var]
  | Syntax.Stmt.Seq (st1, st2) -> compile st1 @ compile st2
