From LinearCore Require
  BoundIn
  Map
  Term
  .
From LinearCore Require Import
  Invert
  .


Inductive Term : Term.term -> String.string -> Prop :=
  | Mov name
      : Term (Term.Mov name) name
  | Ref name
      : Term (Term.Ref name) name
  | ApF function name (used_in_function : Term function name) argument
      : Term (Term.App function argument) name
  | ApA argument name (used_in_argument : Term argument name) function
      : Term (Term.App function argument) name
  | FoT type name (used_in_type : Term type name) variable body
      : Term (Term.For variable type body) name
  | FoB name variable (not_shadowed : name <> variable) body (used_in_body : Term body name) type
      : Term (Term.For variable type body) name
  | CaB pattern name (not_shadowed : forall (B : BoundIn.Pattern pattern name), False)
      body_if_match (used_in_body : Term body_if_match name) other_cases
      : Term (Term.Cas pattern body_if_match other_cases) name
  | CaO other_cases name (used_in_another_case : Term other_cases name) pattern body_if_match
      : Term (Term.Cas pattern body_if_match other_cases) name
  .
Arguments Term term name.

Fixpoint term t : Map.set :=
  match t with
  | Term.Mov name | Term.Ref name =>
      Map.singleton name tt
  | Term.App function argument =>
      Map.set_union (term function) (term argument)
  | Term.For variable type body =>
      Map.set_union (term type) (Map.remove variable (term body))
  | Term.Cas pattern body_if_match other_cases =>
      Map.set_union (term other_cases) (Map.minus (term body_if_match) (BoundIn.pattern pattern))
  | _ => Map.empty
  end.

Lemma term_spec t
  : Map.Reflect (Term t) (term t).
Proof.
  induction t; cbn in *; intros.
  - split. { intros [v F]. invert F. } intro T. invert T.
  - split. { intros [v F]. apply Map.find_singleton in F as [-> ->]. constructor. }
    intro T. invert T. eexists. apply Map.find_singleton. split; reflexivity.
  - split. { intros [v F]. apply Map.find_singleton in F as [-> ->]. constructor. }
    intro T. invert T. eexists. apply Map.find_singleton. split; reflexivity.
  - split.
    + intros [v F]. eapply Map.union_overriding in F as [F | F];
      [apply ApF; apply IHt1 | apply ApA; apply IHt2 |]; try (eexists; exact F).
      intros ? [] ? []. reflexivity.
    + intro T. invert T; [apply IHt1 in used_in_function as [v IH] | apply IHt2 in used_in_argument as [v IH]];
      eexists; (apply Map.union_overriding; [intros ? [] ? []; reflexivity |]); [left | right]; exact IH.
  - split.
    + intros [v F]. apply Map.union_overriding in F as [F | F]; [| | intros ? [] ? []; reflexivity]. {
        apply FoT. apply IHt1. eexists. exact F. }
      eapply Map.find_remove_if_present in F as [N F]. 2: { apply Map.remove_if_present_remove. }
      apply FoB. { exact N. } apply IHt2. eexists. exact F.
    + intro T. invert T; [apply IHt1 in used_in_type as [v IH] | apply IHt2 in used_in_body as [v IH]];
      eexists; (apply Map.union_overriding; [intros ? [] ? []; reflexivity |]); [left | right]. { exact IH. }
      eapply Map.find_remove_if_present. { apply Map.remove_if_present_remove. } split; eassumption.
  - split.
    + intros [v F]. apply Map.union_overriding in F as [F | F]; [| | intros ? [] ? []; reflexivity]. {
        apply CaO. apply IHt2. eexists. exact F. }
      apply Map.minus_minus in F as [F N]. apply CaB. 2: { eapply IHt1. eexists. exact F. }
      intro B. apply N. apply BoundIn.pattern_iff. exact B.
    + intro T. invert T; [apply IHt1 in used_in_body as [v IH] | apply IHt2 in used_in_another_case as [v IH]];
      eexists; (apply Map.union_overriding; [intros ? [] ? []; reflexivity |]); [right | left]. 2: { exact IH. }
      apply Map.minus_minus. split. { exact IH. } intro B. apply not_shadowed. apply BoundIn.pattern_iff. exact B.
Qed.
