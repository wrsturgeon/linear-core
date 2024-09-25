From LinearCore Require
  Name
  Reflect
  .
From LinearCore Require Import
  Invert
  .

Variant builtin : Set :=
  | Error
  | LargeType
  | Proposition
  | Reference
  .

Definition builtin_eq (a b : builtin) :=
  match a, b with
  | Error, Error
  | LargeType, LargeType
  | Proposition, Proposition
  | Reference, Reference => true
  | _, _ => false
  end.
Arguments builtin_eq a b/.

Lemma builtin_eq_spec a b
  : Reflect.Bool (a = b) (builtin_eq a b).
Proof. destruct a; destruct b; constructor; try solve [intro D; discriminate D]; reflexivity. Qed.



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
  destruct a as [a | a]; destruct b as [b | b]; try (constructor; intro D; discriminate D); unfold eq.
  - destruct (builtin_eq_spec a b); constructor. { subst. reflexivity. }
    intro D. apply N. invert D. reflexivity.
  - destruct (Name.spec a b); subst; constructor. { reflexivity. } intro E. apply N. invert E. reflexivity.
Qed.



From Coq Require Import String.

Definition builtin_to_string builtin : string :=
  match builtin with
  | Error => "!"
  | LargeType => "*"
  | Proposition => "?"
  | Reference => "&"
  end.

Definition to_string ctor : string :=
  match ctor with
  | Builtin builtin => builtin_to_string builtin
  | UserDefined name => "<" ++ Name.to_string name ++ ">"
  end.
