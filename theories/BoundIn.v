From LinearCore Require
  Map
  Pattern
  Reflect
  Term
  .
From LinearCore Require Import
  Invert
  .



Definition Reflect {T} (P : T -> Name.name -> Prop) (p : T -> Map.set) : Prop :=
  forall t, Map.Reflect (P t) (p t).
Arguments Reflect {T} P p/.



Inductive Strict : Pattern.strict -> Name.name -> Prop :=
  | SArg curried name
      : Strict (Pattern.App curried name) name
  | SRec curried name (bound_earlier : Strict curried name) argument
      : Strict (Pattern.App curried argument) name
  .

Fixpoint strict s : Map.set :=
  match s with
  | Pattern.Ctr _ => Map.empty
  | Pattern.App curried argument => Map.overriding_add argument tt (strict curried)
  end.

Lemma strict_spec : Reflect Strict strict. Proof.
  split.
  - intro I. generalize dependent x. induction t; intros; cbn in *. { destruct I as [y F]. invert F. }
    apply Map.in_overriding_add in I as [-> | I]; [left | right]. apply IHt. exact I.
  - intro S. induction S; cbn; apply Map.in_overriding_add; [left | right]. { reflexivity. } exact IHS.
Qed.



Variant Pattern : forall (pattern : Pattern.pattern) (name : Name.name), Prop :=
  | PNam name
      : Pattern (Pattern.Nam name) name
  | PPat strict name (bound_in_strict : Strict strict name)
      : Pattern (Pattern.Pat strict) name
  .

Definition pattern p : Map.set :=
  match p with
  | Pattern.Nam name => Map.singleton name tt
  | Pattern.Pat s => strict s
  end.

Lemma pattern_spec : Reflect Pattern pattern. Proof.
  split.
  - intro I. generalize dependent x. induction t; intros; cbn in *.
    + apply Map.in_singleton in I as ->. constructor.
    + constructor. apply strict_spec. exact I.
  - intro S. invert S; cbn.
    + apply Map.in_singleton. reflexivity.
    + apply strict_spec. exact bound_in_strict.
Qed.



(* Bound *anywhere* in a term: not only at the top-level (e.g. in a match) but also arbitrarily far from control flow. *)
Inductive Term : Term.term -> Name.name -> Prop :=
  | TMov name
      : Term (Term.Mov name) name
  | TRef name
      : Term (Term.Ref name) name
  | TApF function name (bound_in_function : Term function name) argument
      : Term (Term.App function argument) name
  | TApA argument name (bound_in_argument : Term argument name) function
      : Term (Term.App function argument) name
  | TFoV name type body
      : Term (Term.For name type body) name
  | TFoT type name (bound_in_type : Term type name) variable body
      : Term (Term.For variable type body) name
  | TFoB body name (bound_in_body : Term body name) variable type
      : Term (Term.For variable type body) name
  | TCaP pattern name (bound_in_pattern : Pattern pattern name) body_if_match other_cases
      : Term (Term.Cas pattern body_if_match other_cases) name
  | TCaB body_if_match name (bound_in_body : Term body_if_match name) pattern other_cases
      : Term (Term.Cas pattern body_if_match other_cases) name
  | TCaO other_cases name (bound_in_other_cases : Term other_cases name) pattern body_if_match
      : Term (Term.Cas pattern body_if_match other_cases) name
  .
Arguments Term term name.

Fixpoint term t : Map.set :=
  match t with
  | Term.Mov name
  | Term.Ref name => Map.singleton name tt
  | Term.App function arg => Map.set_union (term function) (term arg)
  | Term.For variable type body => Map.overriding_add variable tt (Map.set_union (term type) (term body))
  | Term.Cas p body_if_match other_cases => Map.set_union (pattern p) (Map.set_union (term body_if_match) (term other_cases))
  | _ => Map.empty
  end.

Lemma term_spec : Reflect Term term. Proof.
  split.
  - intro I. generalize dependent x. induction t; intros; simpl term in *.
    + apply Map.empty_empty in I as [].
    + apply Map.empty_empty in I as [].
    + apply Map.empty_empty in I as [].
    + apply Map.empty_empty in I as [].
    + apply Map.in_singleton in I as ->. constructor.
    + apply Map.in_singleton in I as ->. constructor.
    + apply Map.in_overriding_union in I as [I | I]; [apply TApF | apply TApA]; [apply IHt1 | apply IHt2]; exact I.
    + apply Map.in_overriding_add in I as [-> | I]. { apply TFoV. }
      apply Map.in_overriding_union in I as [I | I]; [apply TFoT | apply TFoB]; [apply IHt1 | apply IHt2]; exact I.
    + apply Map.in_overriding_union in I as [I | I]. { apply TCaP. apply pattern_spec. exact I. }
      apply Map.in_overriding_union in I as [I | I]; [apply TCaB | apply TCaO]; [apply IHt1 | apply IHt2]; exact I.
  - intro T. induction T; simpl term in *.
    + apply Map.in_singleton. reflexivity.
    + apply Map.in_singleton. reflexivity.
    + apply Map.in_overriding_union. left. exact IHT.
    + apply Map.in_overriding_union. right. exact IHT.
    + apply Map.in_overriding_add. left. reflexivity.
    + apply Map.in_overriding_add. right. apply Map.in_overriding_union. left. exact IHT.
    + apply Map.in_overriding_add. right. apply Map.in_overriding_union. right. exact IHT.
    + apply Map.in_overriding_union. left. apply pattern_spec. exact bound_in_pattern.
    + apply Map.in_overriding_union. right. apply Map.in_overriding_union. left. exact IHT.
    + apply Map.in_overriding_union. right. apply Map.in_overriding_union. right. exact IHT.
Qed.
