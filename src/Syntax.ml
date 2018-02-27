(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let int_of_bool b = if b then 1 else 0
    let bool_of_int i = i != 0
  
    let rec eval st e = 
      match e with
    | Const c -> c
    | Var v -> st v
    | Binop (op, ex1, ex2) ->
        let v1 = eval st ex1 in
        let v2 = eval st ex2 in
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

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval conf stmt = 
      match conf, stmt with
      | (st, el::i, o), Read var -> (Expr.update var el st, i, o)
      | (st, i, o), Write exp -> (st, i, o@[Expr.eval st exp])
      | (st, i, o), Assign (var, exp) -> (Expr.update var (Expr.eval st exp) st, i, o)
      | _, Seq (stmt_f, stmt_s) -> eval (eval conf stmt_f) stmt_s
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
