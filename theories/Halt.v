From Coq.extraction Require
  Extraction
  .
From LinearCore Require Import
  DollarSign
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



From Coq Require Import String.

Definition to_string {T} format (h : halt T) : string :=
  match h with
  | Return x => "Halt.Return (" ++ format x ++ ")"
  | Exit => "Halt.Exit"
  | OutOfFuel => "Halt.OutOfFuel"
  end.
