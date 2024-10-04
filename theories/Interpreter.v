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
  (fun context term => Term.nodes term + List.fold_right (fun kv =>
    Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context)) lt.
Proof. apply Telescopes.wf_tele_measure. exact Subterm.lt_wf. Qed.

Lemma pull_out_of_acc add acc (li : list (MapCore.key * Term.term))
  : List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) (add + acc) li =
    add + List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) acc li.
Proof.
  generalize dependent acc. generalize dependent add.
  induction li as [| [k v] tail IH]; intros; cbn in *. { reflexivity. }
  rewrite PeanoNat.Nat.add_assoc. rewrite (PeanoNat.Nat.add_comm add $ Term.nodes v).
  rewrite <- PeanoNat.Nat.add_assoc. f_equal. apply IH.
Qed.


(*
Equations interpret (context : Context.context) (term : Term.term)
  : Context.context * Term.term by wf (Nat.add (Term.nodes term) $
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 $ MapCore.bindings context) lt :=
  interpret context term with SmallStepFunction.dec context term => {
    | @SmallStepFunction.CouldntStep _ => (context, term)
    | @SmallStepFunction.Stepped _ _ context' term' _ => interpret context' term'
  }.
Next Obligation.
  clear interpret. induction stepped.
  - cbn. destruct no_contraction as [_ R]. assert (R' := Map.remove_if_present_remove name context).
    eapply Map.remove_if_present_det in R'. 2: { exact R. } 2: { reflexivity. } 2: { apply Map.eq_refl. }
    apply Map.bindings_eq in R' as ->. destruct (Map.bindings_remove_split lookup) as [bl [br [-> ->]]].
    repeat rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc. apply PeanoNat.Nat.lt_succ_diag_r.
  - apply PeanoNat.Nat.add_lt_mono_l. eassert (agree : _); [| assert (A :=
      @Map.add_overriding _ self stepped updated_context_without_self agree)]. {
      intros v' F'. contradiction not_overwriting_self. eexists. exact F'. }
    eapply Map.add_det in A. 2: { exact update. } 2: { reflexivity. } 2: { reflexivity. } 2: { apply Map.eq_refl. }
    apply Map.bindings_eq in A as ->. destruct (Map.bindings_add_split not_overwriting_self stepped) as [bl [br [Ea Eu]]].
    rewrite Ea. rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc.
    rewrite <- List.fold_right_app. rewrite <- Eu. clear Ea Eu.
    destruct remove_self_from_context as [_ R]. assert (R' := Map.remove_if_present_remove self context).
    eapply Map.remove_if_present_det in R'. 2: { exact R. } 2: { reflexivity. } 2: { apply Map.eq_refl. }
    apply Map.bindings_eq in R'. rewrite R' in IHstepped. destruct (Map.bindings_remove_split lookup) as [bl' [br' [-> Er]]].
    rewrite Er in IHstepped. rewrite List.fold_right_app in *; simpl List.fold_right in *. rewrite pull_out_of_acc. exact IHstepped.
  - cbn. apply -> PeanoNat.Nat.succ_lt_mono. repeat rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument).
    repeat rewrite <- PeanoNat.Nat.add_assoc. apply PeanoNat.Nat.add_lt_mono_l. exact IHstepped.
  - clear compatible_names unshadowed. cbn. repeat rewrite <- (PeanoNat.Nat.add_assoc $ Term.nodes body_if_match).
    do 2 rewrite plus_n_Sm. apply PeanoNat.Nat.add_lt_mono_l. clear body_if_match. invert matched.
    + rename S into A. eassert (agree : _); [| assert (A' := @Map.add_overriding _ name scrutinee context agree)]. {
        intros v' F'. contradiction N. eexists. exact F'. }
      eapply Map.add_det in A'. 2: { exact A. } 2: { reflexivity. } 2: { reflexivity. } 2: { apply Map.eq_refl. }
      apply Map.bindings_eq in A' as ->. destruct (Map.bindings_add_split N scrutinee) as [bl [br [-> ->]]].
      repeat rewrite List.fold_right_app; cbn. rewrite pull_out_of_acc.
      rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes scrutinee). rewrite <- PeanoNat.Nat.add_assoc. do 2 rewrite plus_n_Sm.
      apply PeanoNat.Nat.add_lt_mono_l. repeat rewrite <- PeanoNat.Nat.add_succ_l.
      apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ.
    + invert move_or_reference_matched; rename S into M.
      * generalize dependent other_cases. induction M; intros; cbn in *. {
          rewrite (PeanoNat.Nat.add_comm _ 1). cbn. apply Map.bindings_eq in E as ->.
          repeat rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. }
        eassert (agree : _); [| assert (A' := @Map.add_overriding _ argument_name argument context_with_function_matches agree)]. {
          intros y F. contradiction N. eexists. exact F. }
        eapply Map.add_det in A'; try reflexivity. 2: { exact A. } 2: { apply Map.eq_refl. }
        apply Map.bindings_eq in A' as ->. destruct (Map.bindings_add_split N argument) as [bl [br [E1 E2]]]. rewrite E1.
        rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc. rewrite <- List.fold_right_app. rewrite <- E2.
        rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument). rewrite PeanoNat.Nat.add_succ_r. rewrite PeanoNat.Nat.add_assoc.
        rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument). rewrite PeanoNat.Nat.add_succ_l.
        repeat rewrite <- PeanoNat.Nat.add_assoc. repeat rewrite <- (PeanoNat.Nat.add_succ_r $ Term.nodes argument).
        apply PeanoNat.Nat.add_lt_mono_l. rewrite PeanoNat.Nat.add_assoc. eapply PeanoNat.Nat.lt_trans. { apply IHM. }
        repeat apply -> PeanoNat.Nat.succ_lt_mono. apply PeanoNat.Nat.lt_succ_diag_r.
      * invert follow_references. 2: { edestruct N as []. reflexivity. } clear term F transitive without_self R.
        destruct OW as [[looked_up lookup] OW]. assert (OW' := Map.overwrite_if_present_overwrite name old_context_with_matches cleaved).
        eapply Map.overwrite_if_present_det in OW'; try reflexivity. 2: { exact OW. } 2: { apply Map.eq_refl. }
        apply Map.bindings_eq in OW' as ->. clear context_with_matches OW. cbn. rewrite (PeanoNat.Nat.add_comm _ 1). cbn.
        generalize dependent looked_up. generalize dependent name. generalize dependent other_cases.
        induction M; intros; cbn in *. { apply Map.bindings_eq in E as ->.
          destruct (Map.bindings_overwrite_split lookup $ Term.Ctr ctor) as [bl [br [E1 ->]]]; cbn in E1; rewrite E1; clear E1.
          repeat rewrite List.fold_right_app. cbn. rewrite <- PeanoNat.Nat.add_1_l. repeat rewrite pull_out_of_acc. cbn.
          apply -> PeanoNat.Nat.succ_lt_mono. rewrite PeanoNat.Nat.add_assoc. repeat rewrite <- PeanoNat.Nat.add_succ_l.
          apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. }
        apply A in lookup as [[-> ->] | lookup]. 2: {
          rewrite <- (IHM _ _ _ lookup); clear IHM. assert (E : Map.Eq
            (Map.overriding_add name (Term.App function_cleaved $ Term.Var argument_name Ownership.Owned) context_with_matches)
            (Map.overriding_add name (Term.App function_cleaved $ Term.Var argument_name Ownership.Owned) $
              Map.overriding_add argument_name argument context_with_function_matches)). {
            intros k v. repeat rewrite Map.find_overriding_add. split; (intros [[-> ->] | [N' F]]; [left; split; reflexivity | right]);
            (split; [exact N' |]). 2: { apply A. destruct F as [E | [Nk F]]; [left | right]; [exact E | exact F]. }
            apply A in F as [[-> ->] | F]; [left; split; reflexivity | right].
            split. 2: { exact F. } intros ->. apply N. eexists. exact F. } apply Map.bindings_eq in E as ->.
          destruct (Map.bindings_overwrite_split lookup function_cleaved) as [bl [br [E1 E2]]]; cbn in E1; rewrite E1; clear E1.
          rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc. rewrite <- List.fold_right_app.
          assert (lookup' : Map.Find (Map.overriding_add argument_name argument context_with_function_matches) name looked_up). {
            apply Map.add_overriding. { intros v' F'. contradiction N. eexists. exact F'. } right. exact lookup. }
          destruct (Map.bindings_overwrite_split lookup' $ Term.App function_cleaved $ Term.Var argument_name Ownership.Owned)
            as [bl' [br' [E1' E2']]]; cbn in E1'; rewrite E1'; clear E1' lookup'. rewrite List.fold_right_app. cbn.
          rewrite (PeanoNat.Nat.add_comm _ 1). rewrite <- PeanoNat.Nat.add_1_l. rewrite PeanoNat.Nat.add_assoc.
          rewrite pull_out_of_acc. cbn. repeat rewrite <- PeanoNat.Nat.add_succ_r. apply PeanoNat.Nat.add_lt_mono_l.
          rewrite <- List.fold_right_app. Abort.
Fail Next Obligation.



Theorem terminating context term
  : exists context' term', Interpret context term context' term'.
Proof.
  destruct (interpret context term) as [context' term'] eqn:I.
  exists context'. exists term'. apply interpret_iff. exact I.
Qed. *)
