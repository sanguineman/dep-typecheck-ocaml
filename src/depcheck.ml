open Syntax
open Pp

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

and eval (env: env) (e: exp) : value =
  match e with
  | Var x -> lookup x env
  | App (e1, e2) -> app (eval env e1) (eval env e2)
  | Let (x, e1, _, e3) -> eval (update env x (eval env e1)) e3
  | Type -> VType
  | _ -> VClos (env, e)

(* p.172 2.3. Conversion algorithm *)
let rec whnf (v: value) : value =
  match v with
  | VApp (u, w) -> app (whnf u) w
  | VClos (env, e) -> eval env e
  | _ -> v

(* 값 동치(eqVal). 정수 k는 새 제네릭 값(VGen k) 배정에 사용 *)
let rec eq_val (k, u1, u2) : bool =
  match (whnf u1, whnf u2) with
  | VType, VType -> true
  | VApp (t1, w1), VApp (t2, w2) ->
      eq_val (k, t1, t2) && eq_val (k, w1, w2)
  | VGen k1, VGen k2 -> k1 = k2
  | VClos (env1, Abs (x1, e1)), VClos (env2, Abs (x2, e2)) ->
      let v = VGen k in
      eq_val (k + 1, VClos (update env1 x1 v, e1), VClos (update env2 x2 v, e2))
  | VClos (env1, Pi (x1, a1, b1)), VClos (env2, Pi (x2, a2, b2)) ->
      let v = VGen k in
      eq_val (k, VClos (env1, a1), VClos (env2, a2)) &&
      eq_val (k + 1,
              VClos (update env1 x1 v, b1),
              VClos (update env2 x2 v, b2))
  | _ -> false

(* 타입체커: 감마(gamma)는 타입 환경(식별자 ↦ 타입값), 로(rho)는 값 환경 *)

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
  | Pi (x, a, b) ->
      (match whnf v with
      | VType ->
          check_type (k, rho, gamma) a &&
          let vgen = VGen k in
          let rho'   = update rho x vgen in
          let gamma' = update gamma x (VClos (rho, a)) in
          check_type (k + 1, rho', gamma') b
      | _ -> failwith "expected Type for Pi")
  | Let (x, e1, e2, e3) ->
      check_type (k, rho, gamma) e2 &&
      let rho'   = update rho x (eval rho e1) in
      let gamma' = update gamma x (eval rho e2) in
      check_exp (k, rho', gamma') e3 v
  | _ ->
      (* 기본: infer 한 타입과 기대타입 v가 동치인지 확인 *)
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
          else failwith "application type mismatch"
      | _ -> failwith "application: expected Pi")
  | Type -> VType
  | _ -> failwith "cannot infer type for this expression"

let typecheck (m: exp) (a: exp) : bool =
  check_type (0, [], []) a &&
  check_exp   (0, [], []) m (VClos ([], a))

(* id = λA. λx. x : ΠA:Type. Πx:A. A *)
let sample_check (m : exp) (a : exp) =
  Printf.printf "\n[Checking Expression]\n%s\n" (string_of_exp m);
  Printf.printf "\n[Expected Type]\n%s\n" (string_of_exp a);
  try
    if typecheck m a then
      Printf.printf "\n[Result]\nTypecheck succeeded!\n\n"
    else
      Printf.printf "\n[Result]\nTypecheck failed.\n\n"
  with
  | Failure msg ->
      Printf.printf "\n[Error] %s\n\n" msg
  | Lookup_error x ->
      Printf.printf "\n[Error] Unbound variable: %s\n\n" x
