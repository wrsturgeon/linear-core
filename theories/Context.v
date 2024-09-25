From LinearCore Require
  Map
  Term
  .



Definition context : Type := Map.to Term.term.
Arguments context/.



From Coq Require Import String.

Definition format_pair kv : string := Name.to_string (fst kv) ++ " -> " ++ Term.to_string (snd kv).

Definition to_string ctx : string :=
  "{ " ++ String.concat "; " (List.map format_pair (MapCore.bindings ctx)) ++ "}".
