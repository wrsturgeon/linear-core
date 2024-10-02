From LinearCore Require
  Constructor
  Ownership
  Pattern
  Reflect
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



(* TODO: unify `Mov` and `Ref` with a boolean ownership flag *)
Inductive term : Set :=
  | Ctr (constructor : Constructor.constructor)
  | Var (name : String.string) (ownership : Ownership.ownership)
  | App (function : term) (argument : term)
  | For (variable : String.string) (type : term) (body : term)
  | Cas (pattern : Pattern.pattern) (body_if_match : term) (other_cases : term)
  .

Fixpoint eq a b :=
  match a, b with
  | Ctr a, Ctr b => Constructor.eq a b
  | Var na oa, Var nb ob => andb (String.eqb na nb) (Ownership.eq oa ob)
  | App fa aa, App fb ab => andb (eq fa fb) (eq aa ab)
  | For va ta ba, For vb tb bb => andb (String.eqb va vb) (andb (eq ta tb) (eq ba bb))
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
  - cbn. destruct (String.eqb_spec name name0). 2: { constructor. intro D. apply n. invert D. reflexivity. }
    subst. destruct (Ownership.eq_spec ownership ownership0); constructor. { subst. reflexivity. }
    intro D. apply N. invert D. reflexivity.
  - simpl eq. destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (String.eqb_spec variable variable0); cbn in *. 2: { constructor. intro E. apply n. invert E. reflexivity. }
    destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (Pattern.eq_spec pattern pattern0); cbn in *. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
Qed.



Inductive Subtree : Term.term -> Term.term -> Prop :=
  | SApF function argument
      : Subtree function $ Term.App function argument
  | SApA function argument
      : Subtree argument $ Term.App function argument
  | SFoT variable type body
      : Subtree type $ Term.For variable type body
  | SFoB variable type body
      : Subtree body $ Term.For variable type body
  | SCaB pattern body_if_match other_cases
      : Subtree body_if_match $ Term.For pattern body_if_match other_cases
  | SCaO pattern body_if_match other_cases
      : Subtree other_cases $ Term.For pattern body_if_match other_cases
  .



Fixpoint nodes t :=
  match t with
  | Term.App a b
  | Term.For _ a b
  | Term.Cas _ a b =>
      S $ nodes a + nodes b
  | _ => 1
  end.



From Coq Require Import String.

Fixpoint to_string t : string :=
  match t with
  | Ctr ctor => Constructor.to_string ctor
  | Var name ownership => if Ownership.owned ownership then name else ("&" ++ name)
  | App function argument => "(" ++ to_string function ++ ") (" ++ to_string argument ++ ")"
  | For variable type body => "forall " ++ variable ++ ": " ++ to_string type ++ ", " ++ to_string body
  | Cas pattern body_if_match other_cases => "if match " ++ Pattern.to_string pattern ++ " then " ++ to_string body_if_match ++ " else " ++ to_string other_cases
  end.
