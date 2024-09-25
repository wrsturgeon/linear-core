From Coq Require Import
  extraction.Extraction
  String
  .



Definition verbose_flag : String.string := "LINEAR_CORE_VERBOSE".

Definition is_verbose : bool := false.
Arguments is_verbose/.
Extract Constant is_verbose => "match Sys.getenv_opt verbose_flag with None -> false | Some _ -> true".
Extraction NoInline is_verbose. (* hopefully to check the environment variable once and only once *)



(* unfortunately, OCaml doesn't seem to support the kind of partial application necessary to
 * define the function once depending on the environment variable
 * (since mutability requires some truly strange weak typing logic),
 * so the next-best solution seems to be to check it once, store that in a boolean, then poll that boolean *)
Definition print (side_effect : string) {T} (output : T) := output.
Arguments print/ side_effect {T} output.
Extract Constant print =>
  "fun side_effect output -> if is_verbose then (print_endline side_effect; output) else output".



Definition format {T} f (x : T) := print (f x) x.
