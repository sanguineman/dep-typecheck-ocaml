open Syntax

let rec string_of_exp e =
  match e with
  | Var x -> x
  | App (e1, e2) ->
      "(" ^ string_of_exp e1 ^ " " ^ string_of_exp e2 ^ ")"
  | Abs (x, body) ->
      "λ" ^ x ^ ". " ^ string_of_exp body
  | Pair (e1, e2) ->
      "pair(" ^ string_of_exp e1 ^ ", " ^ string_of_exp e2 ^ ")"
  | Fst e -> "fst(" ^ string_of_exp e ^ ")"
  | Snd e -> "snd(" ^ string_of_exp e ^ ")"
  | Pi (x, a, b) ->
      "Π" ^ x ^ ":" ^ string_of_exp a ^ ". " ^ string_of_exp b
  | Sigma (x, a, b) ->
      "Σ(" ^ x ^ ":" ^ string_of_exp a ^ ")" ^ string_of_exp b
  | Let (x, e1, a, e2) ->
      "let " ^ x ^ " : " ^ string_of_exp a ^ " = " ^ string_of_exp e1 ^
      " in " ^ string_of_exp e2
  | Type -> "Type"
  | Unit -> "Unit"
  | TT -> "TT"
  | Nat -> "Nat"
  | Zero -> "Zero"
  | Succ e -> "Succ(" ^ string_of_exp e ^ ")"
  | Rec (z, s, n, a) ->
    "Rec(" ^ string_of_exp z ^ ", " ^ string_of_exp s ^ ", " ^
    string_of_exp n ^ ", " ^ string_of_exp a ^ ")"


let rec string_of_val v =
  match v with
  | VType -> "Type"
  | VUnit -> "Unit"
  | VTT -> "TT"
  | VGen k -> "g" ^ string_of_int k
  | VApp (v1, v2) ->
      "(" ^ string_of_val v1 ^ " " ^ string_of_val v2 ^ ")"
  | VFst v -> "fst(" ^ string_of_val v ^ ")"
  | VSnd v -> "snd(" ^ string_of_val v ^ ")"
  | VClos (_, Abs (x, body)) ->
      "λ" ^ x ^ ". " ^ string_of_exp body
  | VClos (_, Pi (x, a, b)) ->
      "Π" ^ x ^ ":" ^ string_of_exp a ^ ". " ^ string_of_exp b
  | VClos (_, e) -> string_of_exp e
  | VNat -> "Nat"
  | VZero -> "Zero"
  | VSucc v -> "Succ(" ^ string_of_val v ^ ")"
