From LinearCore Require
  Constructor
  Name
  .



Inductive raw : Set :=
  | Ctr (constructor : Constructor.constructor)
  | App (curried : raw) (argument : Name.name)
  .

Inductive BoundIn : raw -> Name.name -> Prop :=
  | SArg curried name
      : BoundIn (App curried name) name
  | SRec curried name (bound_earlier : BoundIn curried name) argument
      : BoundIn (App curried argument) name
  .
Arguments BoundIn raw name.

Inductive WellFormed : raw -> Prop :=
  | WFCtr constructor
      : WellFormed (Ctr constructor)
  | WFApp curried argument (no_dup_name : forall (B : BoundIn curried argument), False)
      : WellFormed (App curried argument)
  .
Arguments WellFormed raw.



Definition strict : Type := { raw : raw | WellFormed raw }.



Variant pattern : Type :=
  | Nam (name : Name.name)
  | Pat (strict : strict)
  .
