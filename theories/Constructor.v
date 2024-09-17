From LinearCore Require
  Name
  Reflect
  .
From LinearCore Require Import
  Invert
  .

Variant builtin : Set :=
  .

Definition builtin_eq (a b : builtin) := true.
Arguments builtin_eq a b/.

Lemma builtin_eq_spec a b
  : Reflect.Bool (a = b) (builtin_eq a b).
Proof. destruct a. Qed.



Variant constructor : Set :=
  | Builtin (builtin : builtin)
  | UserDefined (name : Name.name)
  .

Definition eq (a b : constructor) :=
  match a, b with
  | Builtin a, Builtin b => builtin_eq a b
  | UserDefined a, UserDefined b => Name.eqb a b
  | _, _ => false
  end.
Arguments eq a b/.

Lemma eq_spec a b
  : Reflect.Bool (a = b) (eq a b).
Proof.
  destruct a as [a | a]; destruct b as [b | b]; try (constructor; tauto).
  cbn. destruct (Name.spec a b); constructor. { subst. reflexivity. } intro C. apply N. invert C. reflexivity.
Qed.
