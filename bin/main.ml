open Deptypcheck
open Syntax

let () =
  let m = Abs ("A", Abs ("x", Var "x")) in
  let a = Pi ("A", Type, Pi ("x", Var "A", Var "A")) in
  Depcheck.sample_check m a
