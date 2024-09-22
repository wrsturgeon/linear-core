From LinearCore Require
  SmallStepFunction
  .

Set Extraction Optimize.
Unset Extraction Conservative Types.
Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction TypeExpand.
Set Extraction Flag 2047.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive option => "option" [ "Some" "None" ] "(fun some none opt -> match opt with None -> none () | Some x -> some x)".
Extract Inductive prod => "( * )" [ "(, )" ].
Extract Inductive sigT => "( * )" [ "(, )" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive unit => "unit" [ "()" ].

Set Extraction Output Directory "ocaml/lib".
Recursive Extraction Library SmallStepFunction.
