From LinearCore Require
  BoundIn
  Pattern
  .



Inductive Strict : Pattern.strict -> Prop :=
  | SCtr constructor
      : Strict (Pattern.Ctr constructor)
  | SApp curried (curried_well_formed : Strict curried) argument (N : forall (B : BoundIn.Strict curried argument), False)
      : Strict (Pattern.App curried argument)
  .
Arguments Strict strict.



Inductive MoveOrReference : Pattern.move_or_reference -> Prop :=
  | MMov strict (strict_well_formed : Strict strict)
      : MoveOrReference (Pattern.Mov strict)
  | MRef strict (strict_well_formed : Strict strict)
      : MoveOrReference (Pattern.Ref strict)
  .
Arguments MoveOrReference move_or_reference.



Inductive Pattern : Pattern.pattern -> Prop :=
  | Nam name
      : Pattern (Pattern.Nam name)
  | Pat move_or_reference (move_or_reference_well_formed : MoveOrReference move_or_reference)
      : Pattern (Pattern.Pat move_or_reference)
  .
Arguments Pattern pattern.
