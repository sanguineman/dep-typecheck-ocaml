open Syntax

exception Lookup_error of string

let update (env: env) (x: id) (u: value) : env = (x, u) :: env

let rec lookup (x: id) (env: env) : value =
  match env with
  | (y, u) :: tl -> if x = y then u else lookup x tl
  | [] -> raise (Lookup_error ("lookup: " ^ x))

(* a short way of writing the whnf algorithm *)
(* p.169 1.2. Models *)
let rec app (u: value) (v: value) : value =
  match u with
  | VClos (env, Abs (x, e)) -> eval (update env x v) e
  | _ -> VApp (u, v)

and proj_l (v: value) : value =
  match v with 
  | VClos (env, Pair (l, _)) -> eval env l 
  | _ -> VFst v

and proj_r (v: value) : value =
  match v with 
  | VClos (env, Pair (_, r)) -> eval env r 
  | _ -> VSnd v

and eval (env: env) (e: exp) : value =
  match e with
  | Var x -> lookup x env
  | App (e1, e2) -> app (eval env e1) (eval env e2)
  | Fst e -> proj_l (eval env e)
  | Snd e -> proj_r (eval env e)
  | Let (x, e1, _, e3) -> eval (update env x (eval env e1)) e3
  | Type -> VType
  | _ -> VClos (env, e)

(* p.172 2.3.1 Weak head normal form  *)
let rec whnf (v: value) : value =
  match v with
  | VApp (u, w) -> app (whnf u) w
  | VFst u -> proj_l u
  | VSnd u -> proj_r u
  | VClos (env, e) -> eval env e
  | _ -> v

(* p.172 2.3.2. Conversion *)
let rec eq_val (k, u1, u2) : bool =
  match (whnf u1, whnf u2) with
  | VType, VType -> true
  | VApp (t1, w1), VApp (t2, w2) ->
      eq_val (k, t1, t2) && eq_val (k, w1, w2)
  | VFst w1, VFst w2 | VSnd w1, VSnd w2 -> eq_val (k, w1, w2)
  | VGen k1, VGen k2 -> k1 = k2
  | VClos (env1, Abs (x1, e1)), VClos (env2, Abs (x2, e2)) ->
      let v = VGen k in
      eq_val (k + 1, VClos (update env1 x1 v, e1), VClos (update env2 x2 v, e2))
  | VClos (env1, Pair (l1, r1)), VClos (env2, Pair (l2, r2)) ->
      eq_val (k, VClos (env1, l1), VClos (env2, l2))
      && eq_val (k, VClos (env1, r1), VClos (env2, r2))
  | VClos (env1, Pi (x1, a1, b1)), VClos (env2, Pi (x2, a2, b2))
  | VClos (env1, Sigma (x1, a1, b1)), VClos (env2, Sigma (x2, a2, b2)) ->
      let v = VGen k in
      eq_val (k, VClos (env1, a1), VClos (env2, a2)) &&
      eq_val (k + 1,
              VClos (update env1 x1 v, b1),
              VClos (update env2 x2 v, b2))
  | _ -> false

(* Gamma is a type environment : id -> type value
   Rho is a value environment  : id -> value *)

(* p.173 2.4. Type-checking algorithm *)
(* type checking and type inference *)
let rec check_type (k, rho, gamma) (e: exp) : bool =
  check_exp (k, rho, gamma) e VType

and check_exp (k, rho, gamma) (e: exp) (v: value) : bool =
  match e with
  | Abs (x, body) ->
      (match whnf v with
      | VClos (env, Pi (y, a, b)) ->
          let v' = VGen k in
          let rho'   = update rho x v' in
          let gamma' = update gamma x (VClos (env, a)) in
          check_exp (k + 1, rho', gamma') body (VClos (update env y v', b))
      | _ -> failwith "expected Pi for abstraction")
  | Pair (l, r) ->
      (match whnf v with
      | VClos (env, Sigma (x, a, b)) ->
          check_exp (k, rho, gamma) l (VClos (env, a)) &&
          check_exp (k, rho, gamma) r
            (VClos (update env x (VClos (rho, l)), b))
      | _ -> failwith "expected Sigma for pair")
  | Pi (x, a, b)
  | Sigma (x, a, b) ->
      (match whnf v with
      | VType ->
          let v' = VGen k in
          let rho'   = update rho x v' in
          let gamma' = update gamma x (VClos (rho, a)) in
          check_type (k, rho, gamma) a &&
          check_type (k + 1, rho', gamma') b
      | _ -> failwith "expected Type")
  | Let (x, e1, e2, e3) ->
      let rho'   = update rho x (eval rho e1) in
      let gamma' = update gamma x (eval rho e2) in
      check_type (k, rho, gamma) e2 &&
      check_exp (k, rho', gamma') e3 v
  | _ ->
      eq_val (k, infer_exp (k, rho, gamma) e, v)

and infer_exp (k, rho, gamma) (e: exp) : value =
  match e with
  | Var id -> lookup id gamma
  | App (e1, e2) ->
      (match whnf (infer_exp (k, rho, gamma) e1) with
      | VClos (env, Pi (x, a, b)) ->
          if check_exp (k, rho, gamma) e2 (VClos (env, a))
          then
            VClos (update env x (VClos (rho, e2)), b)
          else failwith "application error"
      | _ -> failwith "application, expected Pi")
  | Fst e -> 
      (match whnf (infer_exp (k, rho, gamma) e) with
      | VClos (env, Sigma (_x, a, _b)) -> VClos (env, a)
      | _ -> failwith "projection, expected Sigma")
  | Snd e -> 
      (match whnf (infer_exp (k, rho, gamma) e) with
      | VClos (env, Sigma (x, _a, b)) -> 
          VClos (update env x (VClos (rho, Fst e)), b)
      | _ -> failwith "projection, expected Sigma")
  | Type -> VType
  | _ -> failwith "cannot infer type"

let typecheck (m: exp) (a: exp) : bool =
  check_type (0, [], []) a &&
  check_exp   (0, [], []) m (VClos ([], a))