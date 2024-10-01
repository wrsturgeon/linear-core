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
  DollarSign
  Invert
  .



Inductive Step (context : Context.context) : Term.term -> Context.context -> Term.term -> Prop :=
  | Mov
      {name term} (lookup : Map.Find context name term)
      {context_without_name} (no_contraction : Map.Remove name context context_without_name)
      : Step context (Term.Mov name) context_without_name term
  | Ref
      {self term} (lookup : Map.Find context self term)
      {context_without_self} (remove_self_from_context : Map.Remove self context context_without_self)
      {stepped updated_context_without_self} (step_in_context
        : Step context_without_self term updated_context_without_self stepped)
      (not_overwriting_self : forall (I : Map.In updated_context_without_self self), False)
      {context_updated_in_place} (update
        : Map.Add self stepped updated_context_without_self context_updated_in_place)
      : Step context (Term.Ref self) context_updated_in_place (Term.Ref self)
  | ApM
      {pattern} (compatible_names : Match.Compatible context pattern)
      {scrutinee body_if_match other_cases} (unshadowed
        : Unshadow.Unshadowed $ Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)
      {context_with_matches} (matched
        : Match.Pattern context pattern scrutinee context_with_matches)
      : Step context
        (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)
        context_with_matches body_if_match
  | ApS
      {pattern} (compatible_names : Match.Compatible context pattern)
      {scrutinee body_if_match other_cases} (unshadowed
        : Unshadow.Unshadowed $ Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)
      (no_match : forall context_with_matches (M : Match.Pattern context pattern scrutinee context_with_matches), False)
      {updated_context reduced_scrutinee} (reduce_scrutinee : Step context scrutinee updated_context reduced_scrutinee)
      : Step context
        (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)
        updated_context
        (Term.App (Term.Cas pattern body_if_match other_cases) reduced_scrutinee)
  | ApN
      {pattern} (compatible_names : Match.Compatible context pattern)
      {scrutinee body_if_match other_cases} (unshadowed
        : Unshadow.Unshadowed $ Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)
      (no_match : forall context_with_matches (M : Match.Pattern context pattern scrutinee context_with_matches), False)
      {shape} (scrutinee_reduced : Shape.Shape shape scrutinee)
      {unchanged_context} (context_unchanged : Map.Eq context unchanged_context)
      : Step context
        (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee) unchanged_context
        (Term.App other_cases scrutinee)
  | ApR
      {pattern scrutinee body_if_match other_cases} (not_yet_safe_to_match
        : ~Match.Compatible context pattern \/ ~Unshadow.Unshadowed $ Term.App (Term.Cas pattern body_if_match other_cases) scrutinee)
      {context_domain} (D : Map.Domain context context_domain)
      {renamed} (rename : Unshadow.unshadow_reserve context_domain
        (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee) = Some renamed)
      {unchanged_context} (context_unchanged : Map.Eq context unchanged_context)
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
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
  - invert S2.
    + contradiction (no_match c2'). eapply Match.pattern_eq; try reflexivity; try eassumption. 2: { apply Map.eq_refl. }
      apply Map.eq_sym. exact Ec.
    + edestruct IHS1 as [Ec' E]. { exact Ec. } { exact reduce_scrutinee. } subst reduced_scrutinee0.
      split. { exact Ec'. } reflexivity.
    + eapply shapes_cant_step in scrutinee_reduced as []. eassumption.
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
  - invert S2.
    + contradiction (no_match c2'). eapply Match.pattern_eq; try reflexivity; try eassumption. 2: { apply Map.eq_refl. }
      apply Map.eq_sym. exact Ec.
    + eapply shapes_cant_step in scrutinee_reduced as []. eassumption.
    + split. 2: { reflexivity. } eapply Map.eq_trans. { apply Map.eq_sym. exact context_unchanged. }
      eapply Map.eq_trans. { exact Ec. } exact context_unchanged0.
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
  - invert S2.
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; try eassumption. apply Map.eq_sym. assumption.
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; try eassumption. apply Map.eq_sym. assumption.
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; try eassumption. apply Map.eq_sym. assumption.
    + split. { eapply Map.eq_trans. { apply Map.eq_sym. exact context_unchanged. }
        eapply Map.eq_trans. { exact Ec. } exact context_unchanged0. }
      assert (Ed := Map.domain_det D Ec D0).
      eassert (E := Unshadow.det_reserve Ed Logic.eq_refl). erewrite E in rename.
      rewrite rename in rename0. invert rename0. reflexivity.
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
    + exact unshadowed.
    + eapply Match.pattern_eq; try reflexivity; eassumption.
  - constructor.
    + eapply Match.compatible_eq; try reflexivity; eassumption.
    + exact unshadowed.
    + intros. eapply no_match. eapply Match.pattern_eq; try reflexivity;
      try eassumption. { apply Map.eq_sym. eassumption. } apply Map.eq_refl.
    + apply IHS1; eassumption.
  - econstructor.
    + eapply Match.compatible_eq; try reflexivity; eassumption.
    + exact unshadowed.
    + intros. eapply no_match. eapply Match.pattern_eq; try reflexivity;
      try eassumption. { apply Map.eq_sym. eassumption. } apply Map.eq_refl.
    + apply scrutinee_reduced.
    + eapply Map.eq_trans. { apply Map.eq_sym. exact Ec. }
      eapply Map.eq_trans. { exact context_unchanged. } exact Ec'.
  - econstructor.
    + destruct not_yet_safe_to_match as [N | N]; [left | right]; intro C; apply N. 2: { exact C. }
      eapply Match.compatible_eq. 3: { reflexivity. } { exact C. } apply Map.eq_sym. exact Ec.
    + eapply Map.domain_eq. { exact D. } { exact Ec. } apply Map.eq_refl.
    + exact rename.
    + eapply Map.eq_trans. { apply Map.eq_sym. exact Ec. } eapply Map.eq_trans. { exact context_unchanged. } exact Ec'.
Qed.



Theorem unshadowed_invariant {c t c' t'} (S : Step c t c' t')
  (Ut : Unshadow.Unshadowed t) (Uc : Map.ForAll (fun _ => Unshadow.Unshadowed) c)
  : Unshadow.Unshadowed t' /\ Map.ForAll (fun _ => Unshadow.Unshadowed) c'.
Proof.
  generalize dependent Uc. generalize dependent Ut. induction S; intros.
  - split. { eapply Uc. exact lookup. } intros k v F. eapply Uc. apply no_contraction. exact F.
  - split. { constructor. } intros k v F. destruct IHS as [U FA]. { eapply Uc. exact lookup. }
    + intros k' v' F'. apply remove_self_from_context in F' as [N' F']. eapply Uc. exact F'.
    + apply update in F as [[-> ->] | F]. { exact U. } eapply FA. exact F.
  - cbn. invert unshadowed. invert Ut. invert Uf. invert Uf0. split. { exact Ub. } intros.
    eapply Match.unshadow_pattern. { exact Ua. } { exact Uc. } { exact matched. } exact F.
  - invert unshadowed. invert Ut. specialize (IHS Ua Uc) as [IHt IHc]. split.
    + constructor; try eassumption; intros. { eapply disj_f_a0. { exact Bf. } Abort.
(* So, no, this is not worth enforcing. In other words, why have laziness if we're spending compute
 * renaming terms that we might never use? On the other hand, it costs compute to *check* and/or unshadow at every match.
 * TODO: maybe profile this? *)
