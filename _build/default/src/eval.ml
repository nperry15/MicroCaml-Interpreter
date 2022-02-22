open MicroCamlTypes
open Utils

exception TypeError of string
exception DeclareError of string
exception DivByZeroError 

(* Provided functions - DO NOT MODIFY *)

(* Adds mapping [x:v] to environment [env] *)
let extend env x v = (x, ref v)::env

(* Returns [v] if [x:v] is a mapping in [env]; uses the
   most recent if multiple mappings for [x] are present *)
let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then !value else lookup t x

(* Creates a placeholder mapping for [x] in [env]; needed
   for handling recursive definitions *)
let extend_tmp env x = (x, ref (Int 0))::env

(* Updates the (most recent) mapping in [env] for [x] to [v] *)
let rec update env x v =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then (value := v) else update t x v
        
(* Part 1: Evaluating expressions *)

(* Evaluates MicroCaml expression [e] in environment [env],
   returning a value, or throwing an exception on error *)

let rec eval_expr env e = 
  match e with
  | Value(Int x) -> Int x
  | Value(Bool x) -> Bool x
  | Value(String x) -> String x
  | Value(Closure(x,y,z)) -> Closure(x,y,z)
  | ID(x) -> lookup env x
  | Not(x) -> let expression = eval_expr env x in 
              (match expression with
              | Bool(x) -> Bool (not x)
              | _ -> raise (TypeError "Expected type bool"))
  | Binop(operator, expr1, expr2) -> (match operator with
                                  | Add -> let check_eval1 = eval_expr env expr1 in 
                                          let check_eval2 = eval_expr env expr2 in
                                          (match check_eval1 with
                                          | Int(x) -> (match check_eval2 with
                                                    | Int(y) -> Int (x + y)
                                                    | _ -> raise (TypeError "Expected type int"))
                                          | _ -> raise (TypeError "Expected type int"))
                                  | Sub -> let check_eval1 = eval_expr env expr1 in 
                                          let check_eval2 = eval_expr env expr2 in
                                          (match check_eval1 with
                                          | Int(x) -> (match check_eval2 with
                                                    | Int(y) -> Int (x - y)
                                                    | _ -> raise (TypeError "Expected type int"))
                                          | _ -> raise (TypeError "Expected type int"))
                                  | Div -> let check_eval1 = eval_expr env expr1 in 
                                          let check_eval2 = eval_expr env expr2 in
                                          (match check_eval1 with
                                          | Int(x) -> (match check_eval2 with
                                                    | Int(y) -> if y = 0 then raise (DivByZeroError) else Int (x / y)
                                                    | _ -> raise (TypeError "Expected type int"))
                                          | _ -> raise (TypeError "Expected type int"))
                                  | Mult -> let check_eval1 = eval_expr env expr1 in 
                                            let check_eval2 = eval_expr env expr2 in
                                            (match check_eval1 with
                                            | Int(x) -> (match check_eval2 with
                                                      | Int(y) -> Int (x * y)
                                                      | _ -> raise (TypeError "Expected type int"))
                                            | _ -> raise (TypeError "Expected type int"))

                                  | Greater -> let check_eval1 = eval_expr env expr1 in 
                                              let check_eval2 = eval_expr env expr2 in
                                              (match check_eval1 with
                                              | Int(x) -> (match check_eval2 with
                                                        | Int(y) -> Bool (x > y)
                                                        | _ -> raise (TypeError "Expected type int"))
                                              | _ -> raise (TypeError "Expected type int"))
                                  | GreaterEqual -> let check_eval1 = eval_expr env expr1 in 
                                                    let check_eval2 = eval_expr env expr2 in
                                                    (match check_eval1 with
                                                    | Int(x) -> (match check_eval2 with
                                                              | Int(y) -> Bool (x >= y)
                                                              | _ -> raise (TypeError "Expected type int"))
                                                    | _ -> raise (TypeError "Expected type int"))
                                  | Less -> let check_eval1 = eval_expr env expr1 in 
                                            let check_eval2 = eval_expr env expr2 in
                                            (match check_eval1 with
                                            | Int(x) -> (match check_eval2 with
                                                      | Int(y) -> Bool (x < y)
                                                      | _ -> raise (TypeError "Expected type int"))
                                            | _ -> raise (TypeError "Expected type int"))
                                  | LessEqual -> let check_eval1 = eval_expr env expr1 in 
                                                let check_eval2 = eval_expr env expr2 in
                                                (match check_eval1 with
                                                | Int(x) -> (match check_eval2 with
                                                          | Int(y) -> Bool (x <= y)
                                                          | _ -> raise (TypeError "Expected type int"))
                                                | _ -> raise (TypeError "Expected type int"))

                                  | Concat -> let check_eval1 = eval_expr env expr1 in 
                                              let check_eval2 = eval_expr env expr2 in
                                              (match check_eval1 with
                                              | String(x) -> (match check_eval2 with
                                                        | String(y) -> String (x ^ y)
                                                        | _ -> raise (TypeError "Expected type string"))
                                              | _ -> raise (TypeError "Expected type string"))

                                  | Equal -> let check_eval1 = eval_expr env expr1 in 
                                              let check_eval2 = eval_expr env expr2 in
                                              (match check_eval1 with
                                              | String(x) -> (match check_eval2 with
                                                        | String(y) -> Bool (x = y)
                                                        | _ -> raise (TypeError "Cannot compare types"))
                                              | Int(x) -> (match check_eval2 with
                                                        | Int(y) -> Bool (x = y)
                                                        | _ -> raise (TypeError "Cannot compare types"))
                                              | Bool(x) -> (match check_eval2 with
                                                        | Bool(y) -> Bool (x = y)
                                                        | _ -> raise (TypeError "Cannot compare types"))
                                              | _ -> raise (TypeError "Cannot compare types"))
                                  | NotEqual -> let check_eval1 = eval_expr env expr1 in 
                                                let check_eval2 = eval_expr env expr2 in
                                                (match check_eval1 with
                                                | String(x) -> (match check_eval2 with
                                                          | String(y) -> Bool (not(x = y))
                                                          | _ -> raise (TypeError "Cannot compare types"))
                                                | Int(x) -> (match check_eval2 with
                                                          | Int(y) -> Bool (not(x = y))
                                                          | _ -> raise (TypeError "Cannot compare types"))
                                                | Bool(x) -> (match check_eval2 with
                                                          | Bool(y) -> Bool (not(x = y))
                                                          | _ -> raise (TypeError "Cannot compare types"))
                                                | _ -> raise (TypeError "Cannot compare types"))
                                  
                                  | Or -> let check_eval1 = eval_expr env expr1 in 
                                          let check_eval2 = eval_expr env expr2 in
                                          (match check_eval1 with
                                          | Bool(x) -> (match check_eval2 with
                                                    | Bool(y) -> Bool (x || y)
                                                    | _ -> raise (TypeError "Expected type bool"))
                                          | _ -> raise (TypeError "Expected type bool"))

                                  | And -> let check_eval1 = eval_expr env expr1 in 
                                          let check_eval2 = eval_expr env expr2 in
                                          (match check_eval1 with
                                          | Bool(x) -> (match check_eval2 with
                                                    | Bool(y) -> Bool (x && y)
                                                    | _ -> raise (TypeError "Expected type bool"))
                                          | _ -> raise (TypeError "Expected type bool")))
  | If(gaurd, then_b, else_b) -> let bool = eval_expr env gaurd in
                                (match bool with
                                | Bool(x) -> if x then eval_expr env then_b else eval_expr env else_b
                                | _ -> raise (TypeError "Expected type bool"))
  | Let(var, recur, expr1, expr2) -> if recur then
                                        let tmp_env = extend_tmp env var in
                                        update tmp_env var (eval_expr tmp_env expr1) ;
                                        eval_expr tmp_env expr2
                                      else
                                        let new_env = extend env var (eval_expr env expr1) in
                                        eval_expr new_env expr2
                                        
  | Fun(var, expr1) -> Closure(env, var, expr1)
  | FunctionCall(expr1, expr2) -> let close = eval_expr env expr1 in
                                  let exp = eval_expr env expr2 in
                                  (match close with
                                  | Closure(a, x, e) -> let envi = extend a x exp in eval_expr envi e
                                  | _ -> raise (TypeError "Not a function"))

(* Part 2: Evaluating mutop directive *)

(* Evaluates MicroCaml mutop directive [m] in environment [env],
   returning a possibly updated environment paired with
   a value option; throws an exception on error *)
let eval_mutop env m = 
  match m with
  | Def(var, expr) -> let tmp_env = extend_tmp env var in
                      update tmp_env var (eval_expr tmp_env expr) ;
                      (tmp_env, Some(eval_expr tmp_env expr))
  | Expr(x) -> (env, Some (eval_expr env x))
  | NoOp -> (env, None)
  