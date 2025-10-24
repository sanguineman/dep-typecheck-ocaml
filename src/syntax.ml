type id = string

type exp =
  | Var of id
  | App of exp * exp (* M N *)
  | Abs of id * exp (* λx. M *)
  | Let of id * exp * exp * exp  (* let x = M : A in N *)
  | Pi  of id * exp * exp (* (x: M) N *)
  | Type

(* p.170 2.1. Expressions and values *)
type value =
  | VGen of int (* generic values, the set of new variables *)
  | VApp of value * value
  | VType
  | VClos of env * exp

and env = (id * value) list

