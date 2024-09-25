From Coq Require Import
  extraction.Extraction
  String
  .



Definition verbose_flag : String.string := "LINEAR_CORE_VERBOSE".



Definition string (side_effect : string) {T} (output : T) := output.
Arguments string/ side_effect {T} output.

Extract Constant string =>
  "match Sys.getenv_opt verbose with None -> (fun _ x -> x) | Some _ -> (fun side_effect output -> print_endline side_effect; output)".
Extraction NoInline string. (* to check the `VERBOSE` environment variable once and only once *)



Definition format {T} f (x : T) := string (f x) x.
