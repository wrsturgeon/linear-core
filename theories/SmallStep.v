From LinearCore Require
  Context
  Match
  NewNames
  Shape
  Term
  Unshadow
  UsedIn
  .
From LinearCore Require Import
  Invert
  .



Inductive Step (context : Context.context) : Term.term -> Context.context -> Term.term -> Prop :=
  | Mov
      name term (lookup : Map.Find context name term)
      context_without_name (no_contraction : Map.Remove name context context_without_name)
      : Step context (Term.Mov name) context_without_name term
  | Ref
      self term (lookup : Map.Find context self term)
      context_without_self (remove_self_from_context : Map.Remove self context context_without_self)
      stepped updated_context_without_self (step_in_context
        : Step context_without_self term updated_context_without_self stepped)
      (not_overwriting_self : forall (I : Map.In updated_context_without_self self), False)
      context_updated_in_place (update
        : Map.Add self stepped updated_context_without_self context_updated_in_place)
      : Step context (Term.Ref self) context_updated_in_place (Term.Ref self)
  | ApM
      pattern (compatible_names : Match.Compatible context pattern)
      scrutinee (safe_names : forall x (U : UsedIn.Term scrutinee x) (B : BoundIn.Pattern pattern x), False)
      context_with_matches (matched
        : Match.Pattern context pattern scrutinee context_with_matches)
      body_if_match other_cases
      : Step context
        (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)
        context_with_matches body_if_match
  | ApS
      pattern (compatible_names : Match.Compatible context pattern)
      scrutinee (safe_names : forall x (U : UsedIn.Term scrutinee x) (B : BoundIn.Pattern pattern x), False)
      (no_match : forall context_with_matches (M : Match.Pattern context pattern scrutinee context_with_matches), False)
      updated_context reduced_scrutinee (reduce_scrutinee : Step context scrutinee updated_context reduced_scrutinee)
      body_if_match other_cases
      : Step context
        (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)
        updated_context
        (Term.App (Term.Cas pattern body_if_match other_cases) reduced_scrutinee)
  | ApN
      pattern (compatible_names : Match.Compatible context pattern)
      scrutinee (safe_names : forall x (U : UsedIn.Term scrutinee x) (B : BoundIn.Pattern pattern x), False)
      (no_match : forall context_with_matches (M : Match.Pattern context pattern scrutinee context_with_matches), False)
      shape (scrutinee_reduced : Shape.Shape shape scrutinee)
      unchanged_context (context_unchanged : Map.Eq context unchanged_context) body_if_match other_cases
      : Step context
        (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee) unchanged_context
        (Term.App other_cases scrutinee)
  | ApR
      pattern scrutinee (not_yet_safe_to_match
        : ~Match.Compatible context pattern \/ exists x, UsedIn.Term scrutinee x /\ BoundIn.Pattern pattern x)
      body_if_match other_cases other_used (scan_other_used
        (* Note that this removes already bound terms, since `UsedIn` won't shadow: *)
        : Map.Reflect (UsedIn.Term (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)) other_used)
      context_or_used (union_into_context_or_used : Map.Union (Map.domain context) other_used context_or_used)
      renamed (rename : Unshadow.unshadow context_or_used
        (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee) = Some renamed)
      unchanged_context (context_unchanged : Map.Eq context unchanged_context)
      : Step context (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee) unchanged_context renamed
    .
Arguments Step context term updated_context updated_term.



Theorem shapes_cant_step
  {shape term} (shaped : Shape.Shape shape term)
  {context updated_context updated_term} (step : Step context term updated_context updated_term)
  : False.
Proof.
  generalize dependent updated_term. generalize dependent updated_context. generalize dependent context.
  induction shaped; intros; invert step; invert shaped.
Qed.



Theorem det
  {c1 t1 c1' t1'} (S1 : Step c1 t1 c1' t1')
  {c2} (Ec : Map.Eq c1 c2)
  {t2} (Et : t1 = t2)
  {c2' t2'} (S2 : Step c2 t2 c2' t2')
  : Map.Eq c1' c2' /\ t1' = t2'.
Proof.
  subst. rename t2 into t. generalize dependent t2'. generalize dependent c2'. generalize dependent c2.
  induction S1; intros.
  - invert S2. apply Ec in lookup0. destruct (Map.find_det lookup lookup0). split. 2: { reflexivity. }
    eapply Map.remove_det; try reflexivity; eassumption.
  - invert S2. split. 2: { reflexivity. } assert (RD :=
      Map.remove_det remove_self_from_context eq_refl Ec remove_self_from_context0).
    specialize (IHS1 _ RD). apply Ec in lookup0. destruct (Map.find_det lookup lookup0).
    specialize (IHS1 _ _ step_in_context) as [Eu <-]. eapply Map.add_det; try reflexivity; eassumption.
  - invert S2.
    + split. 2: { reflexivity. } eapply Match.pattern_det; try reflexivity; eassumption.
    + contradiction (no_match context_with_matches).
      eapply Match.pattern_eq; try reflexivity; try eassumption; apply Map.eq_refl.
    + contradiction (no_match context_with_matches).
      eapply Match.pattern_eq; try reflexivity; try eassumption; apply Map.eq_refl.
    + destruct not_yet_safe_to_match as [N | N].
      * contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
      * destruct N as [x [U B]]. edestruct safe_names. { exact U. } exact B.
  - invert S2.
    + contradiction (no_match c2'). eapply Match.pattern_eq; try reflexivity; try eassumption. 2: { apply Map.eq_refl. }
      apply Map.eq_sym. exact Ec.
    + edestruct IHS1 as [Ec' E]. { exact Ec. } { exact reduce_scrutinee. } subst reduced_scrutinee0.
      split. { exact Ec'. } reflexivity.
    + eapply shapes_cant_step in scrutinee_reduced as []. eassumption.
    + destruct not_yet_safe_to_match as [N | N].
      * contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
      * destruct N as [x [U B]]. edestruct safe_names. { exact U. } exact B.
  - invert S2.
    + contradiction (no_match c2'). eapply Match.pattern_eq; try reflexivity; try eassumption. 2: { apply Map.eq_refl. }
      apply Map.eq_sym. exact Ec.
    + eapply shapes_cant_step in scrutinee_reduced as []. eassumption.
    + split. 2: { reflexivity. } eapply Map.eq_trans. { apply Map.eq_sym. exact context_unchanged. }
      eapply Map.eq_trans. { exact Ec. } exact context_unchanged0.
    + destruct not_yet_safe_to_match as [N | N].
      * contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
      * destruct N as [x [U B]]. edestruct safe_names. { exact U. } exact B.
  - invert S2.
    + destruct not_yet_safe_to_match as [N | N].
      * contradiction N. eapply Match.compatible_eq; try reflexivity; try eassumption. apply Map.eq_sym. assumption.
      * destruct N as [x [U B]]. edestruct safe_names. { exact U. } exact B.
    + destruct not_yet_safe_to_match as [N | N].
      * contradiction N. eapply Match.compatible_eq; try reflexivity; try eassumption. apply Map.eq_sym. assumption.
      * destruct N as [x [U B]]. edestruct safe_names. { exact U. } exact B.
    + destruct not_yet_safe_to_match as [N | N].
      * contradiction N. eapply Match.compatible_eq; try reflexivity; try eassumption. apply Map.eq_sym. assumption.
      * destruct N as [x [U B]]. edestruct safe_names. { exact U. } exact B.
    + split. { eapply Map.eq_trans. { apply Map.eq_sym. exact context_unchanged. }
        eapply Map.eq_trans. { exact Ec. } exact context_unchanged0. }
      assert (Eou : Map.Eq other_used other_used0). {
        split; intro F; (eassert (I : Map.In _ _); [eexists; exact F |]);
        [apply scan_other_used in I | apply scan_other_used0 in I];
        [apply scan_other_used0 in I | apply scan_other_used in I];
        destruct v; destruct I as [[] F']; exact F'. }
      assert (Ecu : Map.Eq context_or_used context_or_used0). {
        eapply Map.union_det; try eassumption. split; intro F; apply Map.find_domain;
        apply Map.find_domain in F; (eapply Map.in_eq; [| exact F]); [apply Map.eq_sym |]; exact Ec. }
      destruct (@Unshadow.det _ _ Ecu (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee) _ eq_refl).
      rewrite rename0 in rename. invert rename. reflexivity.
Qed.



Lemma eq
  {c1 t1 c1' t1'} (S1 : Step c1 t1 c1' t1')
  {c2} (Ec : Map.Eq c1 c2)
  {t2} (Et : t1 = t2)
  {c2'} (Ec' : Map.Eq c1' c2')
  {t2'} (Et' : t1' = t2')
  : Step c2 t2 c2' t2'.
Proof.
  subst. rename t2 into t. rename t2' into t'. generalize dependent c2'. generalize dependent c2.
  induction S1; intros.
  - constructor. { apply Ec. exact lookup. } destruct no_contraction as [I R]. split.
    + eapply Map.in_eq. { apply Map.eq_sym. exact Ec. } eexists. exact lookup.
    + cbn in *. intros x y. rewrite <- Ec'. rewrite <- Ec. apply R.
  - econstructor.
    + apply Ec. exact lookup.
    + destruct remove_self_from_context as [I R]. split.
      * eapply Map.in_eq. { apply Map.eq_sym. exact Ec. } exact I.
      * cbn in *. intros x y. rewrite R. rewrite Ec. reflexivity.
    + exact S1.
    + exact not_overwriting_self.
    + cbn in *. intros x y. rewrite <- Ec'. apply update.
  - constructor.
    + eapply Match.compatible_eq; try reflexivity; eassumption.
    + intros. eapply safe_names; eassumption.
    + eapply Match.pattern_eq; try reflexivity; eassumption.
  - constructor.
    + eapply Match.compatible_eq; try reflexivity; eassumption.
    + intros. eapply safe_names; eassumption.
    + intros. eapply no_match. eapply Match.pattern_eq; try reflexivity;
      try eassumption. { apply Map.eq_sym. eassumption. } apply Map.eq_refl.
    + apply IHS1; eassumption.
  - econstructor.
    + eapply Match.compatible_eq; try reflexivity; eassumption.
    + intros. eapply safe_names; eassumption.
    + intros. eapply no_match. eapply Match.pattern_eq; try reflexivity;
      try eassumption. { apply Map.eq_sym. eassumption. } apply Map.eq_refl.
    + apply scrutinee_reduced.
    + eapply Map.eq_trans. { apply Map.eq_sym. exact Ec. }
      eapply Map.eq_trans. { exact context_unchanged. } exact Ec'.
  - econstructor.
    + destruct not_yet_safe_to_match as [N | [x [U B]]]; [left | right].
      * intro C. apply N. eapply Match.compatible_eq. 3: { reflexivity. } { exact C. }
        apply Map.eq_sym. exact Ec.
      * exists x. split. { exact U. } exact B.
    + exact scan_other_used.
    + intros k v. unfold Map.Union in union_into_context_or_used. rewrite union_into_context_or_used.
      split; (intros [F | F]; [left | right; exact F]); apply Map.find_domain;
      apply Map.find_domain in F; (eapply Map.in_eq; [| exact F]); [apply Map.eq_sym |]; exact Ec.
    + assumption.
    + eapply Map.eq_trans. { apply Map.eq_sym. exact Ec. } eapply Map.eq_trans. { exact context_unchanged. } exact Ec'.
Qed.
