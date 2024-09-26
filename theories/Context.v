From LinearCore Require
  Map
  Term
  .
From LinearCore Require Import
  DollarSign
  .



Definition context : Type := Map.to Term.term.
Arguments context/.



From Coq Require Import String.

Definition format_pair kv : string := fst kv ++ " -> " ++ Term.to_string $ snd kv.

Definition to_string ctx : string :=
  "{ " ++ String.concat "; " (List.map format_pair $ MapCore.bindings ctx) ++ "}".
