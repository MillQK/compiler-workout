(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> st x
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    (*
    let rec eval_while ((st, _, _) as conf) expr stmt =
      let rec eval_while_loop ((loop_st, _, _) as loop_conf) = 
        if (Expr.eval loop_st expr) <> 0 then eval_while_loop (eval loop_conf stmt) else loop_conf
      in eval_while_loop conf

    let rec eval_repeat ((st, _, _) as conf) expr stmt =
      let rec eval_repeat_loop ((loop_st, _, _) as loop_conf) = 
        let ((next_st, _, _) as next_conf) = eval loop_conf stmt
        if (Expr.eval next_st expr) <> 0 then eval_repeat_loop next_conf else next_conf
      in eval_repeat_loop conf
*)

    let rec eval ((st, i, o) as conf) stmt =
      match stmt with
      | Read    x       -> (match i with z::i' -> (Expr.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write   e       -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (Expr.update x (Expr.eval st e) st, i, o)
      | Seq    (s1, s2) -> eval (eval conf s1) s2
      | Skip            -> conf
      | If (expr, t_stmt, f_stmt) -> if (Expr.eval st expr) <> 0 then eval conf t_stmt else eval conf f_stmt
      | While (expr, w_stmt) -> (
        let rec eval_while_loop ((loop_st, _, _) as loop_conf) = if (Expr.eval loop_st expr) <> 0 then eval_while_loop (eval loop_conf w_stmt) else loop_conf
        in eval_while_loop conf
      )
      | Repeat (r_stmt, expr) -> (
        let rec eval_repeat_loop ((loop_st, _, _) as loop_conf) = 
          let ((next_st, _, _) as next_conf) = eval loop_conf r_stmt in
          if (Expr.eval next_st expr) == 0 then eval_repeat_loop next_conf else next_conf
        in eval_repeat_loop conf
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
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
