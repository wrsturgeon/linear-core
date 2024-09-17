From LinearCore Require
  Constructor
  Name
  Pattern
  .
From LinearCore Require Import
  Invert
  .



Inductive term : Type :=
  | Err
  | Typ
  | Prp
  | Ctr (constructor : Constructor.constructor)
  | Mov (name : Name.name)
  | Ref (name : Name.name)
  | App (function : term) (argument : term)
  | For (variable : Name.name) (type : term) (body : term)
  | Cas (pattern : Pattern.pattern) (body_if_match : term) (other_cases : term)
  .

Fixpoint eq a b :=
  match a, b with
  | Err, Err
  | Typ, Typ
  | Prp, Prp => true
  | Ctr a, Ctr b => Constructor.eq a b
  | Mov a, Mov b
  | Ref a, Ref b => Name.eqb a b
  | App fa aa, App fb ab => andb (eq fa fb) (eq aa ab)
  | For va ta ba, For vb tb bb => andb (Name.eqb va vb) (andb (eq ta tb) (eq ba bb))
  | Cas pa ba oa, For pb bb ob => andb (Pattern.eq pa pb) (andb (eq ba bb) (eq oa ob))
  | _, _ => false
  end.

Lemma eq_spec a b
  : Reflect.Bool (a = b) (eq a b).
Proof.
  generalize dependent b. induction a; destruct b;
  try (constructor; intro D; discriminate D); try (constructor; reflexivity).
  - unfold eq. destruct (Constructor.eq_spec constructor constructor0); constructor. { f_equal. assumption. }
    intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (Name.spec name name0); constructor. { f_equal. assumption. }
    intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (Name.spec name name0); constructor. { f_equal. assumption. }
    intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (Name.spec variable variable0); cbn in *. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (Name.spec variable variable0); cbn in *. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
Qed.
