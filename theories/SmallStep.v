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
      : Step context (Term.Var name Ownership.Owned) context_without_name term
  | Ref
      {self term} (lookup : Map.Find context self term)
      {context_without_self} (remove_self_from_context : Map.Remove self context context_without_self)
      {stepped updated_context_without_self} (step_in_context
        : Step context_without_self term updated_context_without_self stepped)
      (not_overwriting_self : forall (I : Map.In updated_context_without_self self), False)
      {context_updated_in_place} (update
        : Map.Add self stepped updated_context_without_self context_updated_in_place)
      : Step context (Term.Var self Ownership.Referenced) context_updated_in_place $ Term.Var self Ownership.Referenced
  | ApF {function updated_context updated_function}
      (reduce_function : Step context function updated_context updated_function) argument
      : Step context (Term.App function argument) updated_context (Term.App updated_function argument)
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
      {shape} (scrutinee_reduced : Shape.ShapeOrRef context scrutinee shape)
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
  - apply Mov. { apply Ec. exact lookup. } destruct no_contraction as [I R]. split.
    + eapply Map.in_eq. { apply Map.eq_sym. exact Ec. } eexists. exact lookup.
    + cbn in *. intros x y. rewrite <- Ec'. rewrite <- Ec. apply R.
  - eapply Ref.
    + apply Ec. exact lookup.
    + destruct remove_self_from_context as [I R]. split.
      * eapply Map.in_eq. { apply Map.eq_sym. exact Ec. } exact I.
      * cbn in *. intros x y. rewrite R. rewrite Ec. reflexivity.
    + exact S1.
    + exact not_overwriting_self.
    + cbn in *. intros x y. rewrite <- Ec'. apply update.
  - apply ApF. apply IHS1. { exact Ec. } exact Ec'.
  - apply ApM.
    + eapply Match.compatible_eq; try reflexivity; eassumption.
    + exact unshadowed.
    + eapply Match.pattern_eq; try reflexivity; eassumption.
  - apply ApS.
    + eapply Match.compatible_eq; try reflexivity; eassumption.
    + exact unshadowed.
    + intros. eapply no_match. eapply Match.pattern_eq; try reflexivity;
      try eassumption. { apply Map.eq_sym. eassumption. } apply Map.eq_refl.
    + apply IHS1; eassumption.
  - eapply ApN.
    + eapply Match.compatible_eq; try reflexivity; eassumption.
    + exact unshadowed.
    + intros. eapply no_match. eapply Match.pattern_eq; try reflexivity;
      try eassumption. { apply Map.eq_sym. eassumption. } apply Map.eq_refl.
    + eapply Shape.eq_ref. { exact scrutinee_reduced. } { exact Ec. } reflexivity.
    + eapply Map.eq_trans. { apply Map.eq_sym. exact Ec. }
      eapply Map.eq_trans. { exact context_unchanged. } exact Ec'.
  - eapply ApR.
    + destruct not_yet_safe_to_match as [N | N]; [left | right]; intro C; apply N. 2: { exact C. }
      eapply Match.compatible_eq. 3: { reflexivity. } { exact C. } apply Map.eq_sym. exact Ec.
    + eapply Map.domain_eq. { exact D. } { exact Ec. } apply Map.eq_refl.
    + exact rename.
    + eapply Map.eq_trans. { apply Map.eq_sym. exact Ec. } eapply Map.eq_trans. { exact context_unchanged. } exact Ec'.
Qed.



Theorem shapes_cant_step
  {term shape} (shaped : Shape.ShapeOf term shape)
  {context updated_context updated_term} (step : Step context term updated_context updated_term)
  : False.
Proof.
  generalize dependent updated_term. generalize dependent updated_context. generalize dependent context.
  induction shaped; intros; invert step; invert shaped. { invert reduce_function. } apply IHshaped in reduce_function as [].
Qed.

Theorem shape_or_ref_cant_step
  {context term shape} (shaped : Shape.ShapeOrRef context term shape)
  {updated_context updated_term} (step : Step context term updated_context updated_term)
  : False.
Proof.
  invert shaped. 2: { eapply shapes_cant_step; eassumption. } generalize dependent shaped0. generalize dependent updated_term.
  generalize dependent updated_context. generalize dependent shape. induction follow_references; intros; cbn in *; subst. {
    invert step. destruct (Map.find_det lookup lookup0). eapply shapes_cant_step. { exact shaped0. } exact step_in_context. }
  invert step. destruct (Map.find_det lookup lookup0). eapply IHfollow_references. 2: { exact shaped0. }
  eapply eq; try reflexivity. { exact step_in_context. } 2: { apply Map.eq_refl. }
  eapply Map.remove_det; try eassumption. { reflexivity. } apply Map.eq_refl.
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
    + specialize (IHS1 _ Ec _ _ reduce_function) as [E ->]. split. { exact E. } reflexivity.
    + eapply shapes_cant_step in S1 as []. constructor.
    + eapply shapes_cant_step in S1 as []. constructor.
    + eapply shapes_cant_step in S1 as []. constructor.
    + eapply shapes_cant_step in S1 as []. constructor.
  - invert S2.
    + eapply shapes_cant_step in reduce_function as []. constructor.
    + split. 2: { reflexivity. } eapply Match.pattern_det; try reflexivity; eassumption.
    + contradiction (no_match context_with_matches).
      eapply Match.pattern_eq; try reflexivity; try eassumption; apply Map.eq_refl.
    + contradiction (no_match context_with_matches).
      eapply Match.pattern_eq; try reflexivity; try eassumption; apply Map.eq_refl.
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
  - invert S2.
    + eapply shapes_cant_step in reduce_function as []. constructor.
    + contradiction (no_match c2'). eapply Match.pattern_eq; try reflexivity; try eassumption. 2: { apply Map.eq_refl. }
      apply Map.eq_sym. exact Ec.
    + edestruct IHS1 as [Ec' E]. { exact Ec. } { exact reduce_scrutinee. } subst reduced_scrutinee0.
      split. { exact Ec'. } reflexivity.
    + eapply shape_or_ref_cant_step in scrutinee_reduced as [].
      eapply eq. { exact S1. } { exact Ec. } { reflexivity. } { apply Map.eq_refl. } reflexivity.
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
  - invert S2.
    + eapply shapes_cant_step in reduce_function as []. constructor.
    + contradiction (no_match c2'). eapply Match.pattern_eq; try reflexivity; try eassumption. 2: { apply Map.eq_refl. }
      apply Map.eq_sym. exact Ec.
    + eapply shape_or_ref_cant_step in scrutinee_reduced as [].
      eapply eq. { exact reduce_scrutinee. } { apply Map.eq_sym. exact Ec. } { reflexivity. } { apply Map.eq_refl. } reflexivity.
    + split. 2: { reflexivity. } eapply Map.eq_trans. { apply Map.eq_sym. exact context_unchanged. }
      eapply Map.eq_trans. { exact Ec. } exact context_unchanged0.
    + destruct not_yet_safe_to_match as [N | N]. 2: { apply N in unshadowed as []. }
      contradiction N. eapply Match.compatible_eq; try reflexivity; eassumption.
  - invert S2.
    + eapply shapes_cant_step in reduce_function as []. constructor.
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



Lemma unused_in {c t c' t'} (S : Step c t c' t')
  {x} (N : forall (U : UsedIn.Indirect c t x), False) (I : Map.In c x)
  : Map.In c' x.
Proof.
  destruct I as [y F]. generalize dependent y. generalize dependent x. induction S; intros.
  - eexists. apply no_contraction. split. { intros ->. apply N. constructor. } exact F.
  - eapply Map.in_add. { exact update. } destruct (String.eqb_spec x self); [left | right]. { exact e. }
    eapply IHS. 2: { apply remove_self_from_context. split. { exact n. } exact F. }
    intro U. apply N. eapply UsedIn.ITransitive. { split. { exact lookup. } apply Map.remove_if_present_remove. }
    eapply UsedIn.indirect_superset. { exact U. }
    intros k v F'. apply remove_self_from_context in F' as [N' F'].
    apply Map.remove_if_present_remove. split. { exact N'. } exact F'.
  - eapply IHS. 2: { exact F. } intro U. apply N. apply UsedIn.IApF. exact U.
  - invert matched.
    + eapply Map.in_add. { exact S. } destruct (String.eqb_spec x name); [left | right]. { exact e. } eexists. exact F.
    + eapply Match.in_move_or_reference. { exact move_or_reference_matched. } right. eexists. exact F.
  - eapply IHS. 2: { exact F. } intro U. apply N. apply UsedIn.IApA. exact U.
  - eapply Map.in_eq. { apply Map.eq_sym. exact context_unchanged. } eexists. exact F.
  - eapply Map.in_eq. { apply Map.eq_sym. exact context_unchanged. } eexists. exact F.
Qed.

Definition AllUsed context term : Prop :=
  Map.ForAll (fun k _ => UsedIn.Indirect context term k) context.
Arguments AllUsed context term/.

Theorem no_memory_leaks {c t} (AU : AllUsed c t) {c' t'} (S : Step c t c' t')
  : AllUsed c' t'.
Proof.
  generalize dependent AU. induction S; cbn in *; intros.
  - destruct no_contraction as [_ no_contraction]. apply no_contraction in F as [N F].
    specialize (AU _ _ F). invert AU. 2: { contradiction N. reflexivity. }
    destruct F0 as [Fc R]. destruct (Map.find_det lookup Fc).
    eapply UsedIn.indirect_superset. { exact transitive. }
    intros k' v' F'. apply R in F' as [N' F']. apply no_contraction. split. { exact N'. } exact F'.
  - apply update in F as [[-> ->] | F]. { constructor. } econstructor.
    + split. { apply update. left. split; reflexivity. } apply Map.remove_if_present_remove.
    + eapply UsedIn.indirect_superset; [eapply IHS |]. 2: { exact F. } 2: {
        intros k' v' F'. apply Map.remove_if_present_remove.
        split. { intros ->. apply not_overwriting_self. eexists. exact F'. }
        apply update. right. exact F'. }
      intros k' v' F'. apply remove_self_from_context in F' as [N' F']. specialize (AU _ _ F').
      invert AU. 2: { contradiction N'. reflexivity. } destruct F0 as [Fc R]. destruct (Map.find_det lookup Fc).
      eapply UsedIn.indirect_superset. { exact transitive. } intros k'' v'' F''. apply R in F'' as [F'' N''].
      apply remove_self_from_context. split. { exact F''. } exact N''.
  - destruct (Map.in_spec (UsedIn.indirect updated_context argument) k); [apply UsedIn.IApA | apply UsedIn.IApF]. {
      apply UsedIn.indirect_spec. exact Y. } rename N into Ni. assert (N : ~UsedIn.Indirect updated_context argument k). {
      intro B. apply Ni. apply UsedIn.indirect_spec. exact B. } clear Ni.
    eapply IHS; clear IHS. 2: { exact F. } intros k' v' F'. specialize (AU _ _ F').
    invert AU. { exact used_in_function. } Abort. (* This case should be true with 90% certainty, but this might be a dead end *)
    (* I'm pretty sure that this is straight-up not true in most of the following cases *)
