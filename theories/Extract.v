Require Import
  ExtrOcamlBasic
  ExtrOcamlNativeString
  .
From LinearCore Require
  Unshadow
  .

Set Extraction Optimize.
Unset Extraction Conservative Types.
Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction TypeExpand.
Set Extraction Flag 2047.
Extraction Blacklist String List.

Extract Inductive sigT => "( * )" [ "(, )" ].

Set Extraction Output Directory "ocaml/lib".
Recursive Extraction Library Unshadow.
