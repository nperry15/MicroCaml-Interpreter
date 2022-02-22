open MicroCamlTypes
open Utils
open TokenTypes

(* Provided functions - DO NOT MODIFY *)

(* Matches the next token in the list, throwing an error if it doesn't match the given token *)
let match_token (toks: token list) (tok: token) =
  match toks with
  | [] -> raise (InvalidInputException(string_of_token tok))
  | h::t when h = tok -> t
  | h::_ -> raise (InvalidInputException(
      Printf.sprintf "Expected %s from input %s, got %s"
        (string_of_token tok)
        (string_of_list string_of_token toks)
        (string_of_token h)))

(* Matches a sequence of tokens given as the second list in the order in which they appear, throwing an error if they don't match *)
let match_many (toks: token list) (to_match: token list) =
  List.fold_left match_token toks to_match

(* Return the next token in the token list as an option *)
let lookahead (toks: token list) = 
  match toks with
  | [] -> None
  | h::t -> Some h

(* Return the token at the nth index in the token list as an option*)
let rec lookahead_many (toks: token list) (n: int) = 
  match toks, n with
  | h::_, 0 -> Some h
  | _::t, n when n > 0 -> lookahead_many t (n-1)
  | _ -> None

(* PASTE YOUR PARSERS FROM P4A HERE *)

let rec parse_expr toks = 
  match toks with
  | (Tok_Let)::t -> let left_over = (match_token toks (Tok_Let)) 
                      in (parse_let left_over)
  | (Tok_Fun)::t -> let left_over = (match_token toks (Tok_Fun)) 
                      in (parse_fun left_over)
  | (Tok_If)::t -> (parse_if toks)

  | _ -> parse_or toks
and parse_if tok =
match tok with
  | Tok_If::t -> let no_If = match_token tok (Tok_If) in
                    let (left_over, exp1_tok) = parse_expr no_If in
                    let no_Then = match_token left_over Tok_Then in
                    let (left_over2, exp2_tok) = parse_expr no_Then in
                    let no_Else = match_token left_over2 Tok_Else in
                    let (left_over3, exp3_tok) = parse_expr no_Else in
                    (left_over3, If(exp1_tok, exp2_tok, exp3_tok))
  | _ -> raise (InvalidInputException("Parse If Error"))

and parse_fun tok =
  match tok with
  | Tok_ID(x)::t -> let no_ID = match_token tok (Tok_ID(x)) in
                    let no_arrow = match_token no_ID Tok_Arrow in
                    let (left_over, exp1_tok) = parse_expr no_arrow in
                    (left_over, Fun(x, exp1_tok))
  | _ -> raise (InvalidInputException("Parse Fun Error"))

and parse_let tok =
  let bool = parse_rec tok in
  let new_tok = if bool then (match_token tok (Tok_Rec)) else tok in
  match new_tok with
  | (Tok_ID(x))::t -> let no_ID = match_token new_tok (Tok_ID(x)) in
                      let no_Equal = match_token no_ID Tok_Equal in
                      let (t_next, exp_tok) = parse_expr no_Equal in
                        let exp1_tok = match_token t_next Tok_In in
                        let (left_over, exp2_tok) = parse_expr exp1_tok in
                        (left_over, Let(x, bool, exp_tok, exp2_tok))
  | _ -> raise (InvalidInputException("Parse Let Error"))

 and parse_letEquals tok = 
  match tok with
	| Tok_Equal::t -> (match_token tok Tok_Equal)
	| _ -> raise (InvalidInputException("No Let Equals"))

and parse_rec tok =
(*  let look = lookahead tok in *)
  match tok with
  | Tok_Rec::t -> true
  | _ -> false

and parse_primary tok = 
	match tok with
	| Tok_Int(x)::t -> let left_over = (match_token tok (Tok_Int(x))) 
                        in (left_over, Value(Int(x)))

	| Tok_Bool(x)::t -> let left_over = (match_token tok (Tok_Bool(x))) 
                        in (left_over, Value(Bool(x)))
  | Tok_String(x)::t -> let left_over = (match_token tok (Tok_String(x))) 
                        in (left_over, Value(String(x)))
	| Tok_ID(x)::t -> let left_over = (match_token tok (Tok_ID(x))) 
                        in (left_over, ID(x))

  | Tok_LParen::t -> let no_LParen = match_token tok Tok_LParen in 
                  let (left_over, ran) = parse_expr no_LParen in 
                  let no_RParen = match_token left_over Tok_RParen in
                  (no_RParen, ran)
  | t -> raise (InvalidInputException(string_of_list string_of_token t))

and parse_or tok = 
	let (left_over, exp) = (parse_and tok) in
		match left_over with
		| Tok_Or::t -> let (left_again, sec_exp) = (parse_or (match_token left_over Tok_Or)) 
                        in (left_again, Binop(Or,exp,sec_exp))
		| _ -> (left_over, exp)

and parse_and tok = 
	let (left_over, exp) = (parse_equal tok) in
		match left_over with
		| Tok_And::t -> let (left_again, sec_exp) = (parse_and (match_token left_over Tok_And)) 
                        in (left_again, Binop(And,exp,sec_exp))
		| _ -> (left_over, exp)

and parse_functionCall tok =
  let (n_tok, exp) = parse_primary tok in
  match n_tok with
  | Tok_Int(x)::t -> let (tok1, exp1) = parse_primary n_tok in
                        (tok1, FunctionCall(exp, exp1))
  | Tok_Bool(x)::t -> let (tok1, exp1) = parse_primary n_tok in
                        (tok1, FunctionCall(exp, exp1))
  | Tok_String(x)::t -> let (tok1, exp1) = parse_primary n_tok in
                        (tok1, FunctionCall(exp, exp1))
  | Tok_ID(x)::t -> let (tok1, exp1) = parse_primary n_tok in
                        (tok1, FunctionCall(exp, exp1))
  | Tok_LParen::t -> let (tok1, exp1) = parse_primary n_tok in
                        (tok1, FunctionCall(exp, exp1))
  | _ -> (n_tok, exp)


and parse_unary tok = 
  match tok with
	| Tok_Not::t -> let (left_again, sec_exp) = (parse_unary (match_token tok Tok_Not)) 
                  in (left_again, Not(sec_exp))
	| _ -> (parse_functionCall tok)

and parse_concat tok = 
	let (left_over, exp) = (parse_unary tok) in
		match left_over with
		| Tok_Concat::t -> let (left_again, sec_exp) = (parse_concat (match_token left_over Tok_Concat)) 
                      in (left_again, Binop(Concat,exp,sec_exp))
		| _ -> (left_over, exp)

and parse_multiply tok = 
	let (left_over, exp) = (parse_concat tok) in
		match left_over with
		| Tok_Mult::t -> let (left_again, sec_exp) = (parse_multiply (match_token left_over Tok_Mult)) 
                      in (left_again, Binop(Mult,exp,sec_exp))

		| Tok_Div::t -> let (left_again, sec_exp) = (parse_multiply (match_token left_over Tok_Div)) 
                      in (left_again, Binop(Div,exp,sec_exp))
		| _ -> (left_over, exp)

and parse_add tok = 
	let (left_over, exp) = (parse_multiply tok) in
		match left_over with
		| Tok_Add::t -> let (left_again, sec_exp) = (parse_add (match_token left_over Tok_Add)) 
                      in (left_again, Binop(Add,exp,sec_exp))

		| Tok_Sub::t -> let (left_again, sec_exp) = (parse_add (match_token left_over Tok_Sub)) 
                      in (left_again, Binop(Sub,exp,sec_exp))
		| _ -> (left_over, exp)

and parse_relational tok = 
		let (left_over, exp) = (parse_add tok) in
		match left_over with

		| Tok_Less::t -> let (left_again, sec_exp) = (parse_relational (match_token left_over Tok_Less)) 
                      in (left_again, Binop(Less,exp,sec_exp))

		| Tok_Greater::t -> let (left_again, sec_exp) = (parse_relational (match_token left_over Tok_Greater)) 
                          in (left_again, Binop(Greater, exp,sec_exp))

		| Tok_LessEqual::t -> let (left_again, sec_exp) = (parse_relational (match_token left_over Tok_LessEqual)) 
                            in (left_again, Binop(LessEqual,exp,sec_exp))

		| Tok_GreaterEqual::t -> let (left_again, sec_exp) = (parse_relational (match_token left_over Tok_GreaterEqual)) 
                              in (left_again, Binop(GreaterEqual,exp,sec_exp))

		| _ -> (left_over, exp) 

and parse_equal tok = 
	let (left_over, exp) = (parse_relational tok) in
		match left_over with
		| Tok_Equal::t -> let (left_again, sec_exp) = (parse_equal (match_token left_over Tok_Equal)) 
                        in (left_again, Binop(Equal,exp,sec_exp))
    | Tok_NotEqual::t -> let (left_again, sec_exp) = (parse_equal (match_token left_over Tok_NotEqual)) 
                        in (left_again, Binop(NotEqual,exp,sec_exp))
		| _ -> (left_over, exp)

(* Part 3: Parsing mutop *)

let rec parse_mutop toks =
  match toks with
  | Tok_Def::t -> let no_Def = match_token toks Tok_Def in 
                      (match no_Def with
                      | Tok_ID(x)::t -> let no_ID = match_token no_Def (Tok_ID(x)) in 
                                          let no_Equal = match_token no_ID (Tok_Equal) in
                                          let (a, b) = parse_expr no_Equal in
                                          let (c, d) = (match a with
                                                | Tok_DoubleSemi::t -> let new_c = match_token a (Tok_DoubleSemi) in (new_c, b)
                                                | _ -> raise (InvalidInputException "No Semi for Def")) in (c, Def(x, d))
                                                  
                                | _ -> raise (InvalidInputException "No ID for Def"))

  | Tok_DoubleSemi::t -> let (a, b) = parse_DoubleSemi toks in (a, NoOp)
  | t -> let (a, b) = parse_expr t in 
                        let (c, d) = (match a with
                                    | Tok_DoubleSemi::t -> let new_c = match_token a (Tok_DoubleSemi) in (new_c, b)
                                    | _ -> raise (InvalidInputException "No Semi for Def")) in (c, Expr(d))

and parse_DoubleSemi tok =
  match tok with
	| Tok_DoubleSemi::t -> ([], match_token tok Tok_DoubleSemi)
	| _ -> raise (InvalidInputException "Double Semi")
