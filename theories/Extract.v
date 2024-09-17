From LinearCore Require
  Match
  .

Set Extraction Optimize.
Unset Extraction Conservative Types.
Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction TypeExpand.
Set Extraction Flag 2047.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive prod => "( * )" [ "(, )" ].
Extract Inductive sigT => "( * )" [ "(, )" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive unit => "unit" [ "()" ].

Set Extraction Output Directory "ocaml/lib".
Recursive Extraction Library Map.
