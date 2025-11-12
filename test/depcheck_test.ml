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
  (* λA B x. x *)
  let m = abs_list ["A"; "B"; "x"] (Var "x") in
  (* (A:Type) -> (B:Type) ->(x:Σ(y:A)B) -> Σ(y:A)B *)
  let t = Sigma ("y", Var "A", Var "B") in
  let a = pi_list [("A", Type); ("B", Type); ("x", t)] t in
  assert (Depcheck.typecheck m a)

let sigma3 () =
  (* λA B x. let a = fst(x) : A; let b = snd(x) : B; a *)
  let m = abs_list ["A"; "B"; "x"] (
    Let ("a", Fst (Var "x"), Var "A",
    Let ("b", Snd (Var "x"), Var "B", Var "a"))) in
  (* (A:Type) -> (B:Type) -> (x:Σ(y:A)B) -> A *)
  let a = pi_list [("A", Type); ("B", Type); ("x", Sigma ("y", Var "A", Var "B"))] (Var "A") in
  assert (Depcheck.typecheck m a)

let sigma4 () =
  (* λA f x. let a = f x : snd(A); a *)
  let m = abs_list ["A"; "f"; "x"]
    (Let ("a", App (Var "f", Var "x"), Snd (Var "A"),  Var "a")) in
  (* (A:Σ(y:Type)Type) -> (f:(t:fst(A))-> snd(A)) -> (x:fst(A)) -> snd(A) *)
  let tA = Sigma ("y", Type, Type) in
  let tf = Pi ("t", Fst (Var "A"), Snd (Var "A")) in
  let a = pi_list [("A", tA); ("f", tf); ("x", Fst (Var "A"))] (Snd (Var "A")) in
  assert (Depcheck.typecheck m a)

let sigma5 () =
  (* λA f x. let a = f x : fst(A); a *)
  let m = abs_list ["A"; "f"; "x"]
    (Let ("a", App (Var "f", Var "x"), Fst (Var "A"),  Var "a")) in
  (* (A:Σ(y:Type)Type) -> (f:(t:snd(A))-> fst(A)) -> (x:snd(A)) -> fst(A) *)
  let tA = Sigma ("y", Type, Type) in
  let tf = Pi ("t", Snd (Var "A"), Fst (Var "A")) in
  let a = pi_list [("A", tA); ("f", tf); ("x", Snd (Var "A"))] (Fst (Var "A")) in
  assert (Depcheck.typecheck m a)

let sigma6 () =
  (* λA B x y.
    let p = pair(x, y) : Σ(z:A)B;
    let a = fst(p) : A;
    let b = snd(p) : B;
    pair(a, b) *)
  let m = abs_list ["A"; "B"; "x"; "y"]
    (Let ("p", Pair (Var "x", Var "y"), Sigma ("z", Var "A", Var "B"),
     Let ("a", Fst (Var "p"), Var "A",
     Let ("b", Snd (Var "p"), Var "B",
     Pair (Var "a", Var "b"))))) in
  (* (A:Type) -> (B:Type) -> (x:A) -> (y:B) -> Σ(z:A)B *)
  let a = pi_list [("A", Type); ("B", Type); ("x", Var "A"); ("y", Var "B")]
    (Sigma ("z", Var "A", Var "B")) in
  assert (Depcheck.typecheck m a)

let let1 () =
  (* let f = (λA. A) : Type -> Type; f *)
  let m = Let ("f", Abs ("X", Var "X"), Pi ("x", Type, Type), Var "f") in
  (* Type -> Type *)
  let a = Pi("x", Type, Type) in
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
          Let ("F", abs_list ["g"; "x"] (App(Var "g", App(Var "g", Var "x"))), Pi("x", Pi("x", Type, Type), Pi("x", Type, Type)),
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

let let6 () =
  (* λA f x. let g = (λy. f y) : ((y:A) -> A); let a = g x : A; a *)
  let m = abs_list ["A"; "f"; "x"]
    (Let ("g", Abs ("y", App (Var "f", Var "y")), Pi ("y", Var "A", Var "A"),
     Let ("a", App (Var "g", Var "x"), Var "A", Var "a"))) in
  (* (A:Type) -> (f:(t:A)->A) -> (x:A) -> A *)
  let tf = pi_list [("t", Var "A")] (Var "A") in
  let a = pi_list [("A", Type); ("f", tf); ("x", Var "A")] (Var "A") in
  assert (Depcheck.typecheck m a)

let unit1 () =
  assert (Depcheck.typecheck Unit Type)

let unit2 () =
  assert (Depcheck.typecheck TT Unit)

let unit3 () =
  let m = Let ("u", TT, Unit, Var "u") in
  assert (Depcheck.typecheck m Unit)

let bool1 () =
  assert (Depcheck.typecheck True Bool);
  assert (Depcheck.typecheck False Bool);
  assert (Depcheck.typecheck Bool Type)

let bool2 () =
  (* if(false, true, true, (λb. Bool)) *)
  let m = If(False, True, True, Abs("b", Bool)) in
  let a = Bool in
  assert (Depcheck.typecheck m a)

let bool3 () =
  (* Acts like Large Elimination *)
  (* if(Unit, Bool, false, (λb. Type)) *)
  let m = If(Unit, Bool, False, Abs("x", Type)) in
  let a = Type in
  assert (Depcheck.typecheck m a)

let bool4 () =
  (* Outermost Type Depends on Term *)
  (* if(tt, false, true, (λb. if(Unit, Bool, b, (λx. Bool)))) *)
  let m = If(TT, False, True, Abs("b", If(Unit, Bool, Var "b", Abs ("x", Type)))) in
  let a = Unit in
  assert (Depcheck.typecheck m a)

let coprod1 () =
  assert (Depcheck.typecheck (Coprod(Unit, Bool)) Type);
  assert (Depcheck.typecheck (Inl(TT)) (Coprod(Unit, Bool)));
  assert (Depcheck.typecheck (Inr(False)) (Coprod(Unit, Bool)))

let coprod2 () =
  let _m = Case (Abs ("x", True), Abs ("x", False), Var "p", Abs ("x", Bool)) in
  let m = Let ("p", Inl(TT), Coprod(Unit, Bool), _m) in
  let a = Bool in
  assert (Depcheck.typecheck m a)

let coprod3 () =
  let __m = Case (Abs ("x", Unit), Abs ("x", Bool), Var "x", Abs ("x", Type)) in
  let _m = Case (Abs ("x", TT), Abs ("x", False), Var "p", Abs ("x", __m)) in
  let m = Let ("p", Inr(False), Coprod(Unit, Bool), _m) in
  let a = Bool in
  assert (Depcheck.typecheck m a)

let nat1 () =
  assert (Depcheck.typecheck Zero Nat)

let nat2 () =
  assert (Depcheck.typecheck (Succ (Succ Zero)) Nat)

let nat3 () =
  let m = Rec (TT, Abs ("y", Abs ("z", TT)), Succ (Succ Zero), Abs ("w", Unit)) in
  assert (Depcheck.typecheck m Unit)

let nat4 () =
  let m = Rec (TT, Abs ("y", Abs ("z", TT)), Zero, Abs ("w", Unit)) in
  assert (Depcheck.typecheck m Unit)

let nat5 () =
  (* Rec(λx. x, λ_.λf.λy. Succ (f y), Zero, (λ_. (_: Nat) Nat) *)
  let plus0 = Rec (Abs ("x", Var "x"), Abs ("z", Abs ("f", Abs("y", Succ (App (Var "f", Var "y"))))), Zero, Abs ("z", Pi ("z", Nat, Nat))) in
  assert (Depcheck.typecheck plus0 (Pi ("y", Nat, Nat)))

let nat6 () =
  (* Rec(λx. x, λ_.λf.λy. Succ (f y), Succ (Succ Zero), (λ_. (_: Nat) Nat) *)
  let plus2 = Rec (Abs ("x", Var "x"), Abs ("z", Abs ("f", Abs("y", Succ (App (Var "f", Var "y"))))), Succ (Succ Zero), Abs ("z", Pi ("z", Nat, Nat))) in
  (* plus2 3*)
  let applied = App (plus2, Succ (Succ (Succ Zero))) in
  assert (Depcheck.typecheck applied Nat)

let nat7 () =
  let _m = Rec (Unit, Abs ("x", Abs ("y", Bool)), Var "n", Abs ("z", Type)) in
  let m = Rec (TT, Abs ("x", Abs ("y", True)), Zero, Abs("n", _m)) in
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
  "Sigma6", sigma6;
  "Let1", let1;
  "Let2", let2;
  "Let3", let3;
  "Let4", let4;
  "Let5", let5;
  "Let6", let6;
  "Unit1", unit1;
  "Unit2", unit2;
  "Unit3", unit3;
  "Bool1", bool1;
  "Bool2", bool2;
  "Bool3", bool3;
  "Bool4", bool4;
  "Coprod1", coprod1;
  "Coprod2", coprod2;
  "Coprod3", coprod3;
  "Nat1", nat1;
  "Nat2", nat2;
  "Nat3", nat3;
  "Nat4", nat4;
  "Nat5", nat5;
  "Nat6", nat6;
  "Nat7", nat7;
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
