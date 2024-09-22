From Coq.extraction Require
  Extraction
  .



Inductive halt (T : Type) : Type :=
  | Return (output : T)
  | Exit
  | OutOfFuel
  .
Arguments Return {T} output.
Arguments Exit {T}.
Arguments OutOfFuel {T}.



Extract Inductive halt => "option" [ "Some" "None" "(assert false; None)" ]
  "(fun some none _ opt -> match opt with None -> none () | Some x -> some x)".
