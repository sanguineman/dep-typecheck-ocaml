open Deptypcheck
open Syntax

let abs_list (xs: string list) (e: exp) =
  List.fold_right (fun x acc -> Abs (x, acc)) xs e

let pi_list (ps: (string * exp) list) (e: exp) =
  List.fold_right (fun (s, e) acc -> Pi (s, e, acc)) ps e

let pi1 () =
  (* λA x. x *)
  let m = abs_list ["A"; "x"] (Var "x") in
  (* (A:Type) -> (x:A) -> A *)
  let a = pi_list [("A", Type); ("x", Var "A")] (Var "A") in
  assert (Depcheck.typecheck m a)

let pi2 () =
  (* λA B x y. x *)
  let m = abs_list ["A"; "B"; "x"; "y"] (Var "x") in
  (* (A:Type) -> (B:Type) -> A -> B -> A *)
  let a = pi_list [("A", Type); ("B", Type); ("x", Var "A"); ("y", Var "B")] (Var "A") in
  assert (Depcheck.typecheck m a)

let pi3 () =
  (* λA B C g f x. g (f x) *)
  let m = abs_list ["A"; "B"; "C"; "g"; "f"; "x"] (App (Var "g", App (Var "f", Var "x"))) in
  (* (A:Type) -> (B:Type) -> (C:Type) -> (g:(b:B)->C) -> (f:(a:A)->B) -> (x:A) -> C *)
  let tg = pi_list [("b", Var "B")] (Var "C") in
  let tf = pi_list [("a", Var "A")] (Var "B") in
  let a = pi_list [("A", Type); ("B", Type); ("C", Type); ("g", tg); ("f", tf); ("x", Var "A")] (Var "C") in
  assert (Depcheck.typecheck m a)

let pi4 () =
  (* λA B C f y x. f x y *)
  let m = abs_list ["A"; "B"; "C"; "f"; "y"; "x"] (App (App (Var "f", Var "x"), Var "y")) in
  (* (A:Type) -> (B:Type) -> (C:Type) -> (f:(a:A)->(b:B)->C) -> (y:B) -> (x:A) -> C *)
  let tf = pi_list [("a", Var "A"); ("b", Var "B")] (Var "C") in
  let a = pi_list [("A", Type); ("B", Type); ("C", Type); ("f", tf); ("y", Var "B"); ("x", Var "A")] (Var "C") in
  assert (Depcheck.typecheck m a)

let pi5 () =
  (* λA P h x. h x *)
  let m = abs_list ["A"; "P"; "h"; "x"] (App (Var "h", Var "x")) in
  (* (A:Type) -> (P:(p:A)->Type) -> (h:(y:A)->P y) -> (x:A) -> P x *)
  let tP = pi_list [("p", Var "A")] Type in
  let th = pi_list [("y", Var "A")] (App (Var "P", Var "y")) in
  let a = pi_list [("A", Type); ("P", tP); ("h", th); ("x", Var "A")] (App (Var "P", Var "x")) in
  assert (Depcheck.typecheck m a)

let pi6 () =
  (* λA. A *)
  let m = Abs ("A", Var "A") in
  (* (A:Type) -> Type *)
  let a = Pi ("A", Type, Type) in
  assert (Depcheck.typecheck m a)

let sigma1 () =
  (* (Type, Type) *)
  let m = Pair (Type, Type) in
  (* Σ(A : Type) Type *)
  let a = Sigma ("A", Type, Type) in
  assert (Depcheck.typecheck m a)

let sigma2 () =
  (* λA B x. fst(x) *)
  let m = abs_list ["A"; "B"; "x"] (Fst (Var "x")) in
  (* (A:Type) -> (B:Type) -> (x:Σ(y:A)B) -> A *)
  let a = pi_list [("A", Type); ("B", Type); ("x", Sigma ("y", Var "A", Var "B"))] (Var "A") in
  assert (Depcheck.typecheck m a)

let sigma3 () =
  (* λA B x. snd(x) *)
  let m = abs_list ["A"; "B"; "x"] (Snd (Var "x")) in
  (* (A:Type) -> (B:Type) -> (x:Σ(y:A)B) -> B *)
  let a = pi_list [("A", Type); ("B", Type); ("x", Sigma ("y", Var "A", Var "B"))] (Var "B") in
  assert (Depcheck.typecheck m a)

let sigma4 () =
  (* λA B x. x *)
  let m = abs_list ["A"; "B"; "x"] (Var "x") in
  (* (A:Type) -> (B:Type) ->(x:Σ(y:A)B) -> Σ(y:A)B *)
  let t = Sigma ("y", Var "A", Var "B") in
  let a = pi_list [("A", Type); ("B", Type); ("x", t)] t in
  assert (Depcheck.typecheck m a)

let sigma5 () =
  (* λA B x. let a = fst(x) : A; let b = snd(x) : B; a *)
  let m = abs_list ["A"; "B"; "x"] (
    Let ("a", Fst (Var "x"), Var "A", 
    Let ("b", Snd (Var "x"), Var "B", Var "a"))) in
  (* (A:Type) -> (B:Type) -> (x:Σ(y:A)B) -> A *)
  let a = pi_list [("A", Type); ("B", Type); ("x", Sigma ("y", Var "A", Var "B"))] (Var "A") in
  assert (Depcheck.typecheck m a)

let let1 () =
  (* let f = (λA. A) : Type -> Type; f *)
  let m = Let ("f", Abs ("X", Var "X"), Pi ("_", Type, Type), Var "f") in
  (* Type -> Type *)
  let a = Pi("_", Type, Type) in
  assert (Depcheck.typecheck m a)

let let2 () =
  (* let f = (λX. X) : (X: Type) -> Type; f (f Type) *)
  let m = Let ("f", Abs ("X", Var "X"), Pi ("X", Type, Type), App (Var "f", App (Var "f", Type))) in
  (* Type *)
  let a = Type in
  assert (Depcheck.typecheck m a)

let let3 () =
  (* let f = (let Y = Type : Type; (λX. X)) : (X: Type) -> Type; f Type *)
  let m = Let ("f", Let("Y", Type, Type, Abs ("X", Var "X")), Pi ("X", Type, Type), App (Var "f", Type)) in
  (* Type *)
  let a = Type in
  assert (Depcheck.typecheck m a)

let let4 () =
  (* let f = (λX. (X: Type) -> Type) : (X: Type) -> Type; let F = (λg x. g (g x)) : (g: Type -> Type) -> x: Type -> Type; F f Type *)
  let m = Let ("f", Abs ("X", Pi("X", Type, Var "X")), Pi ("X", Type, Type),
          Let ("F", abs_list ["g"; "x"] (App(Var "g", App(Var "g", Var "x"))), Pi("_", Pi("_", Type, Type), Pi("_", Type, Type)),
          App (App (Var "F", Var "f"), Type))) in
  let a = Type in
  assert (Depcheck.typecheck m a)

let let5 () =
  (* λA P h x. let a = h x : P x; a *)
  let m = abs_list ["A"; "P"; "h"; "x"] (Let("a", App (Var "h", Var "x"), App (Var "P", Var "x"), Var "a")) in
  (* (A:Type) -> (P:(p:A)->Type) -> (h:(y:A)->P y) -> (x:A) -> P x *)
  let tP = pi_list [("p", Var "A")] Type in
  let th = pi_list [("y", Var "A")] (App (Var "P", Var "y")) in
  let a = pi_list [("A", Type); ("P", tP); ("h", th); ("x", Var "A")] (App (Var "P", Var "x")) in
  assert (Depcheck.typecheck m a)

let unit1 () =
  assert (Depcheck.typecheck Unit Type)

let unit2 () =
  assert (Depcheck.typecheck TT Unit)

let unit3 () =
  let m = Let ("u", TT, Unit, Var "u") in
  assert (Depcheck.typecheck m Unit)

let suite = [
  "Pi1", pi1;
  "Pi2", pi2;
  "Pi3", pi3;
  "Pi4", pi4;
  "Pi5", pi5;
  "Pi6", pi6;
  "Sigma1", sigma1;
  "Sigma2", sigma2;
  "Sigma3", sigma3;
  "Sigma4", sigma4;
  "Sigma5", sigma5;
  "Let1", let1;
  "Let2", let2;
  "Let3", let3;
  "Let4", let4;
  "Let5", let5;
  "Unit1", unit1;
  "Unit2", unit2;
  "Unit3", unit3;
]

let unused_suite = [
]

let () =
  ignore unused_suite;
  Printexc.record_backtrace true;
  let failed =
    List.fold_left (fun acc (name, f) ->
      match f () with
      | () -> Printf.printf "PASS: %s\n%!" name; acc
      | exception ex ->
          Printf.eprintf "FAIL: %s (%s)\n%!" name (Printexc.to_string ex);
          acc + 1
    ) 0 suite
  in
  if failed > 0 then exit 1
