From LinearCore Require
  Map
  Pattern
  Term
  .
From LinearCore Require Import
  Invert
  .



Inductive Strict : Pattern.strict -> Term.term -> Map.to Term.term -> Prop :=
  | Ctr matches (E : Map.Empty matches) ctor
      : Strict (Pattern.Ctr ctor) (Term.Ctr ctor) matches
  | App
      function_pattern function function_matches (function_matched : Strict function_pattern function function_matches)
      argument_name (N : forall (I : Map.In function_matches argument_name), False)
      (* can't match the same name twice in the same pattern ^^^ *)
      argument matches (A : Map.Add argument_name argument function_matches matches)
      : Strict (Pattern.App function_pattern argument_name) (Term.App function argument) matches
  .
Arguments Strict strict term matches.

Fixpoint strict pattern term : option (Map.to Term.term) :=
  match pattern, term with
  | Pattern.Ctr constructor_pattern, Term.Ctr constructor =>
      if Constructor.eq constructor_pattern constructor then Some Map.empty else None
  | Pattern.App function_pattern argument_name, Term.App function argument =>
      match strict function_pattern function with None => None | Some function_matches =>
        Map.disjoint_add argument_name argument function_matches
      end
  | _, _ => None
  end.

Lemma strict_det pattern term
  matches1 (S1 : Strict pattern term matches1)
  matches2 (S2 : Strict pattern term matches2)
  : Map.Eq matches1 matches2.
Proof.
  generalize dependent matches2. induction S1; intros; invert S2.
  - split; intro F; [contradiction (E k) | contradiction (E0 k)]; eexists; eassumption.
  - eapply Map.add_det; [exact A | reflexivity | reflexivity | apply Map.eq_refl |].
    eapply Map.add_eq; [exact A0 | reflexivity | reflexivity |].
    apply Map.eq_sym. apply IHS1. exact function_matched.
Qed.

Lemma strict_spec pattern term
  : Reflect.Option (Strict pattern term) (strict pattern term).
Proof.
  generalize dependent term. induction pattern; intros;
  destruct term; try solve [constructor; intros t C; invert C].
  - unfold strict. destruct (Constructor.eq_spec constructor constructor0); constructor.
    + subst. constructor. apply Map.empty_empty.
    + intros t C. invert C. apply N. reflexivity.

  - (* See if the curried constructor matched successfully: *)
    simpl strict. destruct (IHpattern term1) as [function_matches function_matched | N]. 2: {
      constructor. intros t C. invert C. apply N in function_matched as []. }

    (* See if `argument` was already in `function_matches` (i.e. duplicated, i.e. bad) *)
    destruct (Map.find_spec function_matches argument) as [duplicated F | N]. 2: {
      constructor. econstructor. { eassumption. } { intros [y F]. apply N in F as []. }
      apply Map.add_overriding. cbn. intros. apply N in F as []. }
    constructor. intros t C. invert C. apply N; clear N. eexists. eapply strict_det; [| | eassumption]; eassumption.
Qed.



Variant Pattern : Pattern.pattern -> Term.term -> Map.to Term.term -> Prop :=
  | Nam name term matches (S : Map.Singleton name term matches)
      : Pattern (Pattern.Nam name) term matches
  | Pat strict term matches (strict_matched : Strict strict term matches)
      : Pattern (Pattern.Pat strict) term matches
  .
Arguments Pattern pattern term matches.

Definition pattern patt term :=
  match patt with
  | Pattern.Nam name => Some (Map.singleton name term)
  | Pattern.Pat s => strict s term
  end.

Lemma pattern_det patt term
  matches1 (S1 : Pattern patt term matches1)
  matches2 (S2 : Pattern patt term matches2)
  : Map.Eq matches1 matches2.
Proof. invert S1; invert S2. { eapply Map.singleton_det; eassumption. } eapply strict_det; eassumption. Qed.

Lemma pattern_spec patt term
  : Reflect.Option (Pattern patt term) (pattern patt term).
Proof.
  destruct patt; cbn. { constructor. constructor. apply Map.singleton_singleton. }
  destruct (strict_spec strict0 term); constructor. { constructor. exact Y. }
  intros m C. invert C. apply N in strict_matched as [].
Qed.
