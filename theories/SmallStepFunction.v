From LinearCore Require
  Fuel
  Halt
  SmallStep
  Term
  .
From LinearCore Require Import
  Invert
  .



Fixpoint step (fuel : Fuel.fuel) (context : Context.context) (term : Term.term) : Halt.halt (Context.context * Term.term) :=
  match fuel with Fuel.Stop => Halt.OutOfFuel | Fuel.Continue fuel =>
    match term with
    | Term.Mov name =>
        match Map.find context name with
        | None => Halt.Exit
        | Some updated_term => Halt.Return (Map.remove name context, updated_term)
        end
    | Term.Ref self =>
        match Map.find context self with None => Halt.Exit | Some looked_up =>
          let context_without_self := Map.remove self context in
          match step fuel context_without_self looked_up with
          | Halt.Return (updated_context_without_self, stepped) =>
            match Map.find updated_context_without_self self with Some _ => Halt.Exit | None =>
              Halt.Return (Map.overriding_add self stepped updated_context_without_self, Term.Ref self)
            end
          | other => other
          end
        end
    | Term.App (Term.Cas pattern body_if_match other_cases) scrutinee =>
        let used_in_scrutinee := UsedIn.term scrutinee in
        let bound_in_pattern := BoundIn.pattern pattern in
        if andb (Match.compatible context pattern) (Map.disjoint used_in_scrutinee bound_in_pattern) then
          Halt.Exit
        else
          let other_used := UsedIn.term (Term.App (Term.Cas pattern body_if_match other_cases) scrutinee) in
          let reserved := Map.overriding_union (Map.domain context) other_used in
          let new_names := NewNames.generate reserved (BoundIn.pattern pattern) in
          match Rename.pattern new_names pattern with None => Halt.Exit | Some renamed_pattern =>
            let map_body_if_match := Map.bulk_overwrite new_names (Map.to_self (UsedIn.term body_if_match)) in
            match Rename.term map_body_if_match body_if_match with None => Halt.Exit | Some renamed_body_if_match =>
              let map_other_cases := Map.bulk_overwrite new_names (Map.to_self (UsedIn.term other_cases)) in
              match Rename.term map_other_cases other_cases with None => Halt.Exit | Some renamed_other_cases =>
                Halt.Return (context,
                  Term.App (Term.Cas renamed_pattern renamed_body_if_match renamed_other_cases) scrutinee)
              end
            end
          end
    | _ => Halt.Exit
    end
  end.



(*Instance well_founded_cardinality :*)
(*  Classes.WellFounded (Telescopes.tele_measure*)
(*    (Telescopes.ext Context.context (fun _ : Context.context => Telescopes.tip Term.term))*)
(*    nat*)
(*    (fun (context : Context.context) (_ : Term.term) => Map.cardinality context)*)
(*    lt).*)
(*Proof. apply Telescopes.wf_tele_measure. exact Subterm.lt_wf. Qed.*)
(**)
(**)
(**)
(*Equations step (context : Context.context) (term : Term.term)*)
(*  : option (Context.context * Term.term) by wf (Map.cardinality context) lt :=*)
(*  step context (Term.Mov name) := Map.pop context name;*)
(*  step context (Term.Ref self) with Map.found_dec context self => {*)
(*    | Map.NotFound => None;*)
(*    | @Map.Found looked_up _ =>*)
(*        let context_without_self := Map.remove self context in*)
(*        match step context_without_self looked_up with*)
(*        | None => None*)
(*        | Some (updated_context_without_self, stepped) =>*)
(*          match Map.find updated_context_without_self self with Some _ => None | None =>*)
(*            Some (Map.overriding_add self stepped updated_context_without_self, Term.Ref self)*)
(*          end*)
(*        end*)
(*  };*)
(*  step _ _ := None.*)
(*Next Obligation.*)
(*  rewrite Map.cardinality_remove. apply Map.find_iff in Y as E. rewrite E.*)
(*  apply PeanoNat.Nat.lt_pred_l. apply MapCore.bindings_spec1 in Y.*)
(*  unfold Map.cardinality. rewrite MapCore.cardinal_spec. intro D.*)
(*  destruct (MapCore.bindings context). { invert Y. } discriminate D.*)
(*Qed.*)
(*Fail Next Obligation.*)



(*Program Fixpoint step (context : Context.context) {measure (Map.cardinality context)}*)
(*  : Term.term -> option (Context.context * Term.term) := fun term =>*)
(*    match term with*)
(*    | Term.Mov name =>*)
(*        option_map (fun updated_term => (Map.remove name context, updated_term)) (Map.find context name)*)
(*    | Term.Ref self =>*)
(*        match Map.find context self with None => None | Some looked_up =>*)
(*          let context_without_self := Map.remove self context in*)
(*          match step context_without_self looked_up with*)
(*          | None => None*)
(*          | Some (updated_context_without_self, stepped) =>*)
(*            match Map.find updated_context_without_self self with Some _ => None | None =>*)
(*              Some (Map.overriding_add self stepped updated_context_without_self, Term.Ref self)*)
(*            end*)
(*          end*)
(*        end*)
(*    | _ => None*)
(*    end.*)
(*Next Obligation.*)
(*  rewrite Map.cardinality_remove. rewrite <- Heq_anonymous. apply PeanoNat.Nat.lt_pred_l.*)
(*  symmetry in Heq_anonymous. apply Map.find_iff in Heq_anonymous. apply MapCore.bindings_spec1 in Heq_anonymous.*)
(*  unfold Map.cardinality. rewrite MapCore.cardinal_spec. intro D.*)
(*  destruct (MapCore.bindings context). { invert Heq_anonymous. } discriminate D.*)
(*Qed.*)
(*Next Obligation. split; intros self D; discriminate D. Qed.*)
(*Next Obligation. split; intros self D; discriminate D. Qed.*)
(*Next Obligation. split; intros self D; discriminate D. Qed.*)
(*Next Obligation. split; intros self D; discriminate D. Qed.*)
(*Next Obligation. split; intros self D; discriminate D. Qed.*)
(*Next Obligation. split; intros self D; discriminate D. Qed.*)
(*Next Obligation. split; intros self D; discriminate D. Qed.*)
(*Fail Next Obligation.*)



Lemma compatible_andb context pattern term2
  (E : (Match.compatible context pattern && Map.disjoint (UsedIn.term term2) (BoundIn.pattern pattern))%bool = false)
  (compatible_names : Match.Compatible context pattern)
  (safe_names : forall x (U : UsedIn.Term term2 x) (B : BoundIn.Pattern pattern x), False)
  : False.
Proof.
  apply Bool.andb_false_iff in E as [E | E].
  - destruct (Match.compatible_spec context pattern). { discriminate E. } apply N in compatible_names as [].
  - destruct (Map.disjoint_spec (UsedIn.term term2) (BoundIn.pattern pattern)). { discriminate E. }
    apply N; clear N. intros k U B. eapply safe_names. { apply UsedIn.term_spec. exact U. }
    apply BoundIn.pattern_spec. exact B.
Qed.



Theorem spec fuel context term
  : Reflect.Halt (fun pair => SmallStep.Step context term (fst pair) (snd pair)) (step fuel context term).
Proof.
  generalize dependent term. generalize dependent context. induction fuel. { constructor. }
  destruct term; try solve [constructor; intros [updated_context updated_term] S; cbn in *; invert S].
  - cbn in *. destruct (Map.find_spec context name); constructor; cbn in *.
    + constructor. { exact Y. } apply Map.remove_remove. eexists. exact Y.
    + intros [updated_context updated_term] S; cbn in *. invert S. apply N in lookup as [].
  - cbn in *. destruct (Map.find_spec context name). 2: {
      constructor. intros [m t] C; cbn in *. invert C. apply N in lookup as []. }
    destruct (IHfuel (Map.remove name context) x). 3: { constructor. } 2: {
      constructor. intros [m t] C; cbn in *. invert C. eapply (N (_, _)). eapply SmallStep.eq.
      * exact step_in_context.
      * intros x' y'. destruct remove_self_from_context as [I R]. cbn in R. rewrite R.
        destruct (Map.remove_remove I) as [_ R']. cbn in R'. rewrite R'. reflexivity.
      * eapply Map.find_det; eassumption.
      * apply Map.eq_refl.
      * reflexivity. }
    destruct x0 as [updated_context_without_self stepped]; cbn in *.
    destruct (Map.find_spec updated_context_without_self name); constructor. {
      intros [m t] C; cbn in *. invert C.
      eassert (Er : _); [| eassert (Ex : _); [| destruct (SmallStep.det Y0 Er Ex step_in_context) as [D1 D2]]].
      * intros x' y'. destruct remove_self_from_context as [I R]. cbn in R. rewrite R.
        destruct (Map.remove_remove I) as [_ R']. cbn in R'. rewrite R'. reflexivity.
      * eapply Map.find_det; eassumption.
      * subst. apply not_overwriting_self. eexists. apply D1. eassumption. }
    cbn. econstructor. { exact Y. } { apply Map.remove_remove. eexists. exact Y. } { exact Y0. }
    + intros [y F]. apply N in F as [].
    + apply Map.add_overriding. intros v F. apply N in F as [].
  - unfold step. destruct term1 as [| | | | | | | | pattern body_if_match other_cases];
    try solve [constructor; intros [m t] C; invert C]. destruct andb eqn:E. 2: {
      destruct (Rename.pattern_spec (NewNames.generate
        (Map.overriding_union (Map.domain context) (UsedIn.term (Term.App (Term.Cas pattern body_if_match other_cases) term2)))
        (BoundIn.pattern pattern)) pattern). 2: {
        constructor. intros [m t] C; simpl fst in *; simpl snd in *. invert C; try solve [eapply compatible_andb; eassumption].
        eapply N. eapply Rename.pattern_eq; try reflexivity. { exact rename_pattern. }
        erewrite NewNames.generate_det. { apply Map.eq_refl. } 2: { apply Map.eq_refl. }
        intros k []. rewrite (Map.find_iff (Map.overriding_union _ _)). rewrite Map.find_overriding_union.
        unfold Map.Union in union_into_reserved. rewrite union_into_reserved.
        destruct (Map.find_spec (Map.domain context) k) as [[] M | N']. { split. { reflexivity. } left. exact M. }
        assert (A : Map.Find other_used k tt <-> UsedIn.Term (Term.App (Term.Cas pattern body_if_match other_cases) term2) k). {
          cbn in all_other_used_names. rewrite <- all_other_used_names.
          split; [intro F; eexists | intros [[] F]]; exact F. }
        rewrite A. clear A. rewrite <- Map.find_iff. assert (A
          : Map.Find (UsedIn.term (Term.App (Term.Cas pattern body_if_match other_cases) term2)) k tt <->
            UsedIn.Term (Term.App (Term.Cas pattern body_if_match other_cases) term2) k). {
          rewrite <- (UsedIn.term_spec (Term.App (Term.Cas pattern body_if_match other_cases) term2) k).
          split; [intro F; eexists | intros [[] F]]; exact F. } rewrite A. clear A.
        split. { intros [F | F]. { apply N' in F as []. } exact F. } intro F. right. exact F. }
      destruct (Rename.term_spec (Map.bulk_overwrite (NewNames.generate
        (Map.overriding_union (Map.domain context) (UsedIn.term (Term.App (Term.Cas pattern body_if_match other_cases) term2)))
        (BoundIn.pattern pattern)) (Map.to_self (UsedIn.term body_if_match))) body_if_match). 2: {
        constructor. intros [m t] C; simpl fst in *; simpl snd in *. invert C; try solve [eapply compatible_andb; eassumption].
        eapply N. eapply Rename.term_eq; try reflexivity. { exact rename_body_if_match. } clear rename_body_if_match.
        intros k v. unfold Map.BulkOverwrite in overwrite_body_if_match.
        rewrite overwrite_body_if_match; clear overwrite_body_if_match.
        assert (BO := @Map.bulk_overwrite_bulk_overwrite). unfold Map.BulkOverwrite in BO. rewrite BO; clear BO.
        erewrite NewNames.generate_det. { reflexivity. } 2: { apply Map.eq_refl. }
        intros k' []. unfold Map.Union in union_into_reserved. rewrite union_into_reserved.
        repeat rewrite Map.find_iff. rewrite Map.find_overriding_union. split.
        * intros [E' | E']. { rewrite E'. reflexivity. }
          destruct (Map.find_spec (Map.domain context) k') as [[] |]. { reflexivity. }
          eassert (I : Map.In _ _). { eexists. apply Map.find_iff. exact E'. } apply all_other_used_names in I.
          apply UsedIn.term_spec in I as [[] F]. apply Map.find_iff. exact F.
        * intro E'. destruct (Map.find_spec (Map.domain context) k') as [[] F | N']; [left | right]. { reflexivity. }
          eassert (I : Map.In _ _). { eexists. apply Map.find_iff. exact E'. }
          apply UsedIn.term_spec in I. apply all_other_used_names in I as [[] F]. apply Map.find_iff. exact F. }
      destruct (Rename.term_spec (Map.bulk_overwrite (NewNames.generate
        (Map.overriding_union (Map.domain context) (UsedIn.term (Term.App (Term.Cas pattern body_if_match other_cases) term2)))
        (BoundIn.pattern pattern)) (Map.to_self (UsedIn.term other_cases))) other_cases). 2: {
        constructor. intros [m t] C; simpl fst in *; simpl snd in *. invert C; try solve [eapply compatible_andb; eassumption].
        eapply N. eapply Rename.term_eq; try reflexivity. { exact rename_other_cases. } clear rename_other_cases.
        intros k v. unfold Map.BulkOverwrite in overwrite_other_cases.
        rewrite overwrite_other_cases; clear overwrite_other_cases.
        assert (BO := @Map.bulk_overwrite_bulk_overwrite). unfold Map.BulkOverwrite in BO. rewrite BO; clear BO.
        erewrite NewNames.generate_det. { reflexivity. } 2: { apply Map.eq_refl. }
        intros k' []. unfold Map.Union in union_into_reserved. rewrite union_into_reserved.
        repeat rewrite Map.find_iff. rewrite Map.find_overriding_union. split.
        * intros [E' | E']. { rewrite E'. reflexivity. }
          destruct (Map.find_spec (Map.domain context) k') as [[] |]. { reflexivity. }
          eassert (I : Map.In _ _). { eexists. apply Map.find_iff. exact E'. } apply all_other_used_names in I.
          apply UsedIn.term_spec in I as [[] F]. apply Map.find_iff. exact F.
        * intro E'. destruct (Map.find_spec (Map.domain context) k') as [[] F | N']; [left | right]. { reflexivity. }
          eassert (I : Map.In _ _). { eexists. apply Map.find_iff. exact E'. }
          apply UsedIn.term_spec in I. apply all_other_used_names in I as [[] F]. apply Map.find_iff. exact F. }
      constructor; simpl fst in *; simpl snd in *. eapply SmallStep.ApR; try eassumption.
      + apply Bool.andb_false_iff in E as [E | E]; [left | right].
        * intro C. destruct (Match.compatible_spec context pattern). { discriminate E. } apply N in C as [].
        * destruct (Map.disjoint_spec (UsedIn.term term2) (BoundIn.pattern pattern)). { discriminate E. }
          apply Map.not_disjoint_exists in N as [k [Iu Ib]]. exists k.
          split. { apply UsedIn.term_spec. exact Iu. } apply BoundIn.pattern_spec. exact Ib.
      + apply UsedIn.term_spec.
      + apply Map.union_overriding. intros k [] F [] F'. reflexivity.
      + reflexivity.
      + apply Map.bulk_overwrite_bulk_overwrite.
      + apply Map.bulk_overwrite_bulk_overwrite.
      + apply Map.eq_refl. }
    apply Bool.andb_true_iff in E as [Ec Ed]. destruct (Match.compatible_spec context pattern) as [CP |]; invert Ec.
    destruct (Map.disjoint_spec (UsedIn.term term2) (BoundIn.pattern pattern)) as [D |]; invert Ed.
Abort. (* TODO *)
