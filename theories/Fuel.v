From Coq.extraction Require
  Extraction
  .



Inductive fuel : Set :=
  | Stop
  | Continue (pred : fuel)
  .



Extract Inductive fuel => "unit" [ "()" "()" ]
  "(fun _ f () -> f ())".
