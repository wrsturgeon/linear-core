From LinearCore Require
  Constructor
  Name
  Pattern
  .
From LinearCore Require Import
  Invert
  .



(* TODO: make `Err`, `Typ`, & `Prp` constructors? *)
Inductive term : Set :=
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
  | Cas pa ba oa, Cas pb bb ob => andb (Pattern.eq pa pb) (andb (eq ba bb) (eq oa ob))
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
  - simpl eq. destruct (Pattern.eq_spec pattern pattern0); cbn in *. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
Qed.



From Coq Require Import String.

Fixpoint to_string t : string :=
  match t with
  | Err => "!"
  | Typ => "*"
  | Prp => "?"
  | Ctr ctor => Constructor.to_string ctor
  | Mov name => Name.to_string name
  | Ref name => "&" ++ Name.to_string name
  | App function argument => "(" ++ to_string function ++ ") (" ++ to_string argument ++ ")"
  | For variable type body => "forall (" ++ Name.to_string variable ++ ": " ++ to_string type ++ "), " ++ to_string body
  | Cas pattern body_if_match other_cases => "if match " ++ Pattern.to_string pattern ++ " then { " ++ to_string body_if_match ++ " } else " ++ to_string other_cases
  end.
