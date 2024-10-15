From LinearCore Require
  SmallStepFunction
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



Inductive Partial context term : Context.context -> Term.term -> Prop :=
  | PRefl {equivalent_context} (E : Map.Eq context equivalent_context)
      : Partial context term equivalent_context term
  | PTrans {context' term'} (step : SmallStep.Step context term context' term')
      {context'' term''} (transitive : Partial context' term' context'' term'')
      : Partial context term context'' term''
  .

Inductive Interpret context term : Context.context -> Term.term -> Prop :=
  | Refl (cant_step : forall context' term', ~SmallStep.Step context term context' term')
      {equivalent_context} (E : Map.Eq context equivalent_context)
      : Interpret context term equivalent_context term
  | Trans {context' term'} (step : SmallStep.Step context term context' term')
      {context'' term''} (transitive : Interpret context' term' context'' term'')
      : Interpret context term context'' term''
  .



Instance wf : Classes.WellFounded $ Telescopes.tele_measure
  (Telescopes.ext Context.context (fun _ => Telescopes.tip Term.term)) nat
    (fun context term => (* penalty_for_incompatible_match context term + *) Term.nodes term +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context)) lt.
Proof. apply Telescopes.wf_tele_measure. exact Subterm.lt_wf. Qed.



(*
Equations interpret (context : Context.context) (term : Term.term)
  : Context.context * Term.term by wf (
    (* penalty_for_incompatible_match context term + *) Term.nodes term +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context)) lt :=
  interpret context term with SmallStepFunction.dec context term => {
    | @SmallStepFunction.CouldntStep _ => (context, term)
    | @SmallStepFunction.Stepped _ _ context' term' _ => interpret context' term'
  }.
Next Obligation.
  clear interpret. induction stepped.
  - cbn. destruct no_contraction as [_ R]. assert (R' := Map.remove_if_present_remove name context).
    eapply Map.remove_if_present_det in R'. 2: { exact R. } 2: { reflexivity. } 2: { apply Map.eq_refl. }
    apply Map.bindings_eq in R' as ->. destruct (Map.bindings_remove_split lookup) as [bl [br [-> ->]]].
    repeat rewrite List.fold_right_app. cbn. rewrite Match.pull_out_of_acc. (* rewrite <- PeanoNat.Nat.add_assoc.
    rewrite <- PeanoNat.Nat.add_1_l. apply PeanoNat.Nat.add_lt_mono_r. *) apply PeanoNat.Nat.lt_succ_diag_r.
  - apply PeanoNat.Nat.add_lt_mono_l. eassert (agree : _); [| assert (A :=
      @Map.add_overriding _ self stepped updated_context_without_self agree)]. {
      intros v' F'. contradiction not_overwriting_self. eexists. exact F'. }
    eapply Map.add_det in A. 2: { exact update. } 2: { reflexivity. } 2: { reflexivity. } 2: { apply Map.eq_refl. }
    apply Map.bindings_eq in A as ->. destruct (Map.bindings_add_split not_overwriting_self stepped) as [bl [br [Ea Eu]]].
    rewrite Ea. rewrite List.fold_right_app. cbn. rewrite Match.pull_out_of_acc.
    rewrite <- List.fold_right_app. rewrite <- Eu. clear Ea Eu.
    destruct remove_self_from_context as [_ R]. assert (R' := Map.remove_if_present_remove self context).
    eapply Map.remove_if_present_det in R'. 2: { exact R. } 2: { reflexivity. } 2: { apply Map.eq_refl. }
    apply Map.bindings_eq in R'. rewrite R' in IHstepped. destruct (Map.bindings_remove_split lookup) as [bl' [br' [-> Er]]].
    rewrite Er in IHstepped. rewrite List.fold_right_app in *; simpl List.fold_right in *. rewrite Match.pull_out_of_acc. exact IHstepped.
  - cbn. apply -> PeanoNat.Nat.succ_lt_mono. repeat rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument).
    repeat rewrite <- PeanoNat.Nat.add_assoc. apply PeanoNat.Nat.add_lt_mono_l. exact IHstepped.
  - clear compatible_names unshadowed. cbn. rewrite (PeanoNat.Nat.add_comm $ Pattern.nodes _).
    repeat rewrite <- (PeanoNat.Nat.add_assoc $ Term.nodes body_if_match). repeat rewrite (plus_n_Sm $ Term.nodes _).
    apply PeanoNat.Nat.add_lt_mono_l. clear body_if_match. eapply PeanoNat.Nat.lt_trans. { eapply Match.decreasing. exact matched. }
    eapply PeanoNat.Nat.lt_trans; apply PeanoNat.Nat.lt_succ_diag_r.
  - cbn. repeat apply -> PeanoNat.Nat.succ_lt_mono. repeat rewrite <- PeanoNat.Nat.add_assoc.
    repeat apply PeanoNat.Nat.add_lt_mono_l. exact IHstepped.
  - cbn. apply -> PeanoNat.Nat.succ_lt_mono. rewrite <- (PeanoNat.Nat.add_assoc $ Pattern.nodes _).
    rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes other_cases). rewrite PeanoNat.Nat.add_assoc.
    rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes other_cases). repeat rewrite <- PeanoNat.Nat.add_assoc.
    rewrite <- PeanoNat.Nat.add_succ_r. apply PeanoNat.Nat.add_lt_mono_l.
    rewrite (PeanoNat.Nat.add_assoc _ $ Term.nodes scrutinee). rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes scrutinee).
    repeat rewrite PeanoNat.Nat.add_assoc. rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes scrutinee).
    repeat rewrite <- PeanoNat.Nat.add_assoc. rewrite <- PeanoNat.Nat.add_succ_r. apply PeanoNat.Nat.add_lt_mono_l.
    repeat rewrite PeanoNat.Nat.add_assoc. rewrite <- PeanoNat.Nat.add_succ_l.
    apply Map.bindings_eq in context_unchanged as ->. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ.
  - apply Map.bindings_eq in context_unchanged as <-; clear unchanged_context.
    apply Unshadow.nodes_eq_reserve in rename as ->; clear context_domain D renamed. cbn. Abort.
Fail Next Obligation.



Theorem terminating context term
  : exists context' term', Interpret context term context' term'.
Proof.
  destruct (interpret context term) as [context' term'] eqn:I.
  exists context'. exists term'. apply interpret_iff. exact I.
Qed.
*)
