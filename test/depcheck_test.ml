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

let suite = [
  "Pi1", pi1;
  "Pi2", pi2;
  "Pi3", pi3;
  "Pi4", pi4;
  "Pi5", pi5;
  "Pi6", pi6;
]

let () =
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