type id = string

type exp =
  | Var of id
  | App of exp * exp (* M N *)
  | Abs of id * exp (* λx. M *)
  | Pair of exp * exp (* pair(M, N) *)
  | Fst of exp (* fst(M) *)
  | Snd of exp (* snd(M) *)
  | Let of id * exp * exp * exp (* let x = M : A in N *)
  | Pi of id * exp * exp (* (x: M) N *)
  | Sigma of id * exp * exp (* Σ(x : M) N *)
  | Type
  | Unit (* unit type *)
  | TT (* unit term *)
  | Bool (* Boolean type *)
  | True (* true term *)
  | False (* false term *)
  | If of exp * exp * exp * exp (* if (a_t, a_f, b, A) *)
  | Nat
  | Zero
  | Succ of exp
  | Rec of exp * exp * exp * exp (* Rec(Z,S,N,A) *)

(* p.170 2.1. Expressions and values *)
type value =
  | VGen of int (* generic values, the set of new variables *)
  | VApp of value * value
  | VFst of value
  | VSnd of value
  | VType
  | VClos of env * exp
  | VIf of value * value * value * value
  | VRec of value * value * value * value

and env = (id * value) list

