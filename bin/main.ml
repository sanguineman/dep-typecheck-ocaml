open Deptypcheck
open Syntax

(* id = λA. λx. x : ΠA:Type. Πx:A. A *)
let sample_check (m : exp) (a : exp) =
  Printf.printf "\n[Checking Expression]\n%s\n" (Pp.string_of_exp m);
  Printf.printf "\n[Expected Type]\n%s\n" (Pp.string_of_exp a);
  try
    if Depcheck.typecheck m a then
      Printf.printf "\n[Result]\nTypecheck succeeded!\n\n"
    else
      Printf.printf "\n[Result]\nTypecheck failed.\n\n"
  with
  | Failure msg ->
      Printf.printf "\n[Error] %s\n\n" msg
  | Depcheck.Lookup_error x ->
      Printf.printf "\n[Error] Unbound variable: %s\n\n" x


let () =
  let m = Abs ("A", Abs ("x", Var "x")) in
  let a = Pi ("A", Type, Pi ("x", Var "A", Var "A")) in
  sample_check m a
