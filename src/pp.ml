open Syntax

let rec string_of_exp e =
  match e with
  | Var x -> x
  | App (e1, e2) ->
      "(" ^ string_of_exp e1 ^ " " ^ string_of_exp e2 ^ ")"
  | Abs (x, body) ->
      "λ" ^ x ^ ". " ^ string_of_exp body
  | Pi (x, a, b) ->
      "Π" ^ x ^ ":" ^ string_of_exp a ^ ". " ^ string_of_exp b
  | Let (x, e1, a, e2) ->
      "let " ^ x ^ " : " ^ string_of_exp a ^ " = " ^ string_of_exp e1 ^
      " in " ^ string_of_exp e2
  | Type -> "Type"

let rec string_of_val v =
  match v with
  | VType -> "Type"
  | VGen k -> "g" ^ string_of_int k
  | VApp (v1, v2) ->
      "(" ^ string_of_val v1 ^ " " ^ string_of_val v2 ^ ")"
  | VClos (_, Abs (x, body)) ->
      "λ" ^ x ^ ". " ^ string_of_exp body
  | VClos (_, Pi (x, a, b)) ->
      "Π" ^ x ^ ":" ^ string_of_exp a ^ ". " ^ string_of_exp b
  | VClos (_, e) -> string_of_exp e
