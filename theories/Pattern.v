From LinearCore Require
  Constructor
  Name
  .
From LinearCore Require Import
  Invert
  .



Inductive strict : Set :=
  | Ctr (constructor : Constructor.constructor)
  | App (curried : strict) (argument : Name.name)
  .

Fixpoint strict_eq a b :=
  match a, b with
  | Ctr a, Ctr b => Constructor.eq a b
  | App ca aa, App cb ab => andb (strict_eq ca cb) (Name.eqb aa ab)
  | _, _ => false
  end.

Lemma strict_eq_spec a b
  : Reflect.Bool (a = b) (strict_eq a b).
Proof.
  generalize dependent b. induction a; intros; destruct b.
  - unfold strict_eq. destruct (Constructor.eq_spec constructor constructor0); constructor. { subst. reflexivity. }
    intro E. apply N. invert E. reflexivity.
  - constructor. intro D. discriminate D.
  - constructor. intro D. discriminate D.
  - simpl strict_eq. destruct (IHa b). 2: { constructor. intro E. apply N. invert E. reflexivity. }
    destruct (Name.spec argument argument0); constructor. { subst. reflexivity. } intro E. apply N. invert E. reflexivity.
Qed.



Variant move_or_reference : Set :=
  | Mov (strict : strict)
  | Ref (strict : strict)
  .

Definition move_or_reference_eq a b :=
  match a, b with
  | Mov a, Mov b => strict_eq a b
  | Ref a, Ref b => strict_eq a b
  | _, _ => false
  end.

Lemma move_or_reference_eq_spec a b
  : Reflect.Bool (a = b) (move_or_reference_eq a b).
Proof.
  destruct a; destruct b; cbn.
  - destruct (strict_eq_spec strict0 strict1); constructor. { subst. reflexivity. } intro E. apply N. invert E. reflexivity.
  - constructor. intro D. discriminate D.
  - constructor. intro D. discriminate D.
  - destruct (strict_eq_spec strict0 strict1); constructor. { subst. reflexivity. } intro E. apply N. invert E. reflexivity.
Qed.



Variant pattern : Set :=
  | Nam (name : Name.name)
  | Pat (move_or_reference : move_or_reference)
  .

Definition eq a b :=
  match a, b with
  | Nam a, Nam b => Name.eqb a b
  | Pat a, Pat b => move_or_reference_eq a b
  | _, _ => false
  end.

Lemma eq_spec a b
  : Reflect.Bool (a = b) (eq a b).
Proof.
  destruct a; destruct b; cbn.
  - destruct (Name.spec name name0); constructor. { subst. reflexivity. } intro E. apply N. invert E. reflexivity.
  - constructor. intro D. discriminate D.
  - constructor. intro D. discriminate D.
  - unfold eq. destruct (move_or_reference_eq_spec move_or_reference0 move_or_reference1); constructor. { subst. reflexivity. }
    intro E. apply N. invert E. reflexivity.
Qed.
