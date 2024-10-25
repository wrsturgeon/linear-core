From LinearCore Require
  NewNames
  Rename
  Term
  WellFormed
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



(* NOTE: Even though it's a very unusual case, this has to return an option
 * because patterns (in `Cas`) can be ill-formed if they duplicate a binder. *)
Fixpoint unshadow_acc (acc : Map.to String.string) (cant_bind : Map.set) t :=
  match t with
  | Term.Ctr ctor => Some (cant_bind, Term.Ctr ctor)
  | Term.Var k ownership =>
      (* Have to supply a plan for any free variables (or they have to have been bound & added to the plan): *)
      match Map.find acc k with None => None | Some v => Some (Map.set_add v cant_bind, Term.Var v ownership) end
  | Term.App f a =>
      match unshadow_acc acc cant_bind f with None => None | Some (bound_or_used_f, f') =>
        match unshadow_acc acc bound_or_used_f a with None => None | Some (bound_or_used_a, a') =>
          Some (bound_or_used_a, Term.App f' a')
        end
      end
  | Term.For variable type body =>
      let variable' := NewNames.new_name cant_bind variable in
      let cant_bind_v := Map.set_add variable' cant_bind in
      match unshadow_acc acc cant_bind_v type with None => None | Some (bound_or_used_t, type') =>
        let acc' := Map.overwrite variable variable' acc in
        match unshadow_acc acc' bound_or_used_t body with None => None | Some (bound_or_used_b, body') =>
          Some (bound_or_used_b, Term.For variable' type' body')
        end
      end
  | Term.Cas pattern body_if_match other_cases =>
      let rebindings := NewNames.generate cant_bind (BoundIn.pattern pattern) in
      let cant_bind_p := Map.set_union (Map.range rebindings) cant_bind in
      match unshadow_acc acc cant_bind_p other_cases with None => None | Some (bound_or_used_o, other_cases') =>
        match Rename.pattern rebindings pattern with
        | None => None
        | Some pattern' =>
            let acc' := Map.bulk_overwrite rebindings acc in
            match unshadow_acc acc' bound_or_used_o body_if_match with None => None | Some (bound_or_used_b, body_if_match') =>
              Some (bound_or_used_b, Term.Cas pattern' body_if_match' other_cases')
            end
        end
      end
  end.

Definition unshadow_reserve_bindings cant_bind t :=
  (* let generated := NewNames.generate cant_bind $ UsedIn.term t in *)
  let used := UsedIn.term t in
  let generated := Map.to_self used in
  unshadow_acc generated (Map.set_union cant_bind used) t.
Arguments unshadow_reserve_bindings cant_bind t/.

Definition unshadow_reserve cant_bind t := option_map snd $ unshadow_reserve_bindings cant_bind t.
Arguments unshadow_reserve cant_bind t/.

Definition unshadow := unshadow_reserve Map.empty.
Arguments unshadow/ t.



Lemma unshadow_app acc cant_bind f a
  : unshadow_acc acc cant_bind (Term.App f a) =
    match unshadow_acc acc cant_bind f with None => None | Some (bound_or_used_f, f') =>
      match unshadow_acc acc bound_or_used_f a with None => None | Some (bound_or_used_a, a') =>
        Some (bound_or_used_a, Term.App f' a')
      end
    end.
Proof. reflexivity. Qed.

Lemma unshadow_for acc cant_bind variable type body
  : unshadow_acc acc cant_bind (Term.For variable type body) =
    match
      unshadow_acc acc (Map.set_add (NewNames.new_name cant_bind variable) cant_bind) type
    with None => None | Some (bound_or_used_t, type') =>
      match
        unshadow_acc (Map.overwrite variable (NewNames.new_name cant_bind variable) acc) bound_or_used_t body
      with None => None | Some (bound_or_used_b, body') =>
        Some (bound_or_used_b, Term.For (NewNames.new_name cant_bind variable) type' body')
      end
    end.
Proof. reflexivity. Qed.

Lemma unshadow_cas acc cant_bind pattern body_if_match other_cases
  : unshadow_acc acc cant_bind (Term.Cas pattern body_if_match other_cases) =
    match
      unshadow_acc acc (Map.set_union (Map.range $ NewNames.generate cant_bind (BoundIn.pattern pattern)) cant_bind) other_cases
    with None => None | Some (bound_or_used_o, other_cases') =>
      match
        Rename.pattern (NewNames.generate cant_bind (BoundIn.pattern pattern)) pattern
      with None => None | Some pattern' =>
          match
            unshadow_acc (Map.bulk_overwrite (NewNames.generate cant_bind (BoundIn.pattern pattern)) acc) bound_or_used_o body_if_match
          with None => None | Some (bound_or_used_b, body_if_match') =>
            Some (bound_or_used_b, Term.Cas pattern' body_if_match' other_cases')
          end
      end
    end.
Proof. reflexivity. Qed.



Lemma nodes_eq_acc {acc cant_bind t cant_bind' r} (E : unshadow_acc acc cant_bind t = Some (cant_bind', r))
  : Term.nodes r = Term.nodes t.
Proof.
  generalize dependent r. generalize dependent cant_bind'. generalize dependent cant_bind. generalize dependent acc.
  induction t; intros; cbn in *.
  - invert E. reflexivity.
  - destruct Map.find; invert E. reflexivity.
  - destruct unshadow_acc as [[tmp f'] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[tmp' a'] |] eqn:E2 in E; invert E. cbn.
    specialize (IHt1 _ _ _ _ E1) as ->. specialize (IHt2 _ _ _ _ E2) as ->. reflexivity.
  - destruct unshadow_acc as [[tmp f'] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[tmp' a'] |] eqn:E2 in E; invert E. cbn.
    specialize (IHt1 _ _ _ _ E1) as ->. specialize (IHt2 _ _ _ _ E2) as ->. reflexivity.
  - destruct unshadow_acc as [[tmp f'] |] eqn:E2 in E. 2: { discriminate E. }
    destruct Rename.pattern eqn:Ep. 2: { discriminate E. }
    destruct unshadow_acc as [[tmp' a'] |] eqn:E1 in E; invert E. cbn.
    specialize (IHt1 _ _ _ _ E1) as ->. specialize (IHt2 _ _ _ _ E2) as ->.
    apply Rename.pattern_nodes_eq in Ep as ->. reflexivity.
Qed.

Lemma nodes_eq_reserve {cant_bind t r} (E : unshadow_reserve cant_bind t = Some r)
  : Term.nodes r = Term.nodes t.
Proof.
  unfold unshadow_reserve in E. unfold unshadow_reserve_bindings in E.
  destruct unshadow_acc as [[] |] eqn:E'; invert E. eapply nodes_eq_acc. exact E'.
Qed.

Lemma nodes_eq {t r} (E : unshadow t = Some r)
  : Term.nodes r = Term.nodes t.
Proof. eapply nodes_eq_reserve. exact E. Qed.



Variant Equiv : option (Map.set * Term.term) -> _ -> Prop :=
  | ENone
      : Equiv None None
  | ESome
      {cant_bind1 cant_bind2} (Ecant_bind : Map.Eq cant_bind1 cant_bind2) output
      : Equiv (Some (cant_bind1, output)) (Some (cant_bind2, output))
  .

Lemma det_acc
  {a1 a2} (Ea : Map.Eq a1 a2)
  {r1 r2} (Er : Map.Eq r1 r2)
  {t1 t2} (Et : t1 = t2)
  : Equiv (unshadow_acc a1 r1 t1) (unshadow_acc a2 r2 t2).
Proof.
  subst. rename t2 into t. generalize dependent r2. generalize dependent r1.
  generalize dependent a2. generalize dependent a1. induction t; intros.
  - constructor; assumption.
  - unfold unshadow_acc. destruct (Map.find_spec a1 name).
    + apply Ea in Y. apply Map.find_iff in Y. rewrite Y. constructor. intros k [].
      split; (intro F; apply Map.add_set; apply Map.add_set in F as [[-> _] | F];
        [left | right]; [split; reflexivity | apply Er; exact F]).
    + destruct (Map.find_spec a2 name). { apply Ea in Y. apply N in Y as []. } constructor.
  - cbn. destruct (IHt1 _ _ Ea _ _ Er). { constructor. }
    destruct (IHt2 _ _ Ea _ _ Ecant_bind); constructor; eassumption.
  - repeat rewrite unshadow_for. specialize (IHt1 _ _ Ea $ Map.set_add (NewNames.new_name r1 variable) r1).
    specialize (IHt1 $ Map.set_add (NewNames.new_name r2 variable) r2). destruct IHt1. 2: { constructor. } {
      intros k []. unfold Map.set_add. repeat rewrite Map.find_overriding_add.
      repeat rewrite (NewNames.new_name_det Er). split; (intros [[-> _] | [N F]]; [left | right];
      [split; reflexivity | split; [exact N |]; apply Er; exact F]). }
    specialize (IHt2 $ Map.overwrite variable (NewNames.new_name r1 variable) a1).
    specialize (IHt2 $ Map.overwrite variable (NewNames.new_name r2 variable) a2).
    eassert (Ea' : _); [| specialize (IHt2 Ea')]. {
      intros k v. unfold Map.overwrite. repeat rewrite Map.find_overriding_add. repeat rewrite (NewNames.new_name_det Er).
      split; (intros [[-> ->] | [N F]]; [left | right]; [split; reflexivity | split; [exact N |]; apply Ea; exact F]). }
    specialize (IHt2 cant_bind1 cant_bind2 Ecant_bind) as []. { constructor. }
    repeat rewrite (NewNames.new_name_det Er). constructor. exact Ecant_bind0.
  - repeat rewrite unshadow_cas. rewrite (NewNames.generate_det Er $ Map.eq_refl _).
    specialize (IHt2 _ _ Ea $ Map.set_union (Map.range $ NewNames.generate r2 $ BoundIn.pattern pattern) r1).
    specialize (IHt2 $ Map.set_union (Map.range $ NewNames.generate r2 $ BoundIn.pattern pattern) r2).
    destruct IHt2. 2: { constructor. } { intros k []. repeat rewrite (Map.union_set _ _ _). rewrite (Er k). reflexivity. }
    destruct Rename.pattern eqn:R. 2: { constructor. }
    specialize (IHt1 $ Map.bulk_overwrite (NewNames.generate r2 $ BoundIn.pattern pattern) a1).
    specialize (IHt1 $ Map.bulk_overwrite (NewNames.generate r2 $ BoundIn.pattern pattern) a2).
    eassert (Ea' : _); [| specialize (IHt1 Ea')]. {
      intros k v. repeat rewrite (Map.bulk_overwrite_bulk_overwrite _ _ _). rewrite (Ea k). reflexivity. }
    specialize (IHt1 cant_bind1 cant_bind2 Ecant_bind) as []; constructor. exact Ecant_bind0.
Qed.

Lemma det_bindings {r1 r2} (Er : Map.Eq r1 r2) {t1 t2} (Et : t1 = t2)
  : Equiv (unshadow_reserve_bindings r1 t1) (unshadow_reserve_bindings r2 t2).
Proof.
  subst. rename t2 into t. eapply det_acc. 3: { reflexivity. } { intros k v. reflexivity. }
  intros k v. repeat rewrite (Map.union_set _ _ _). rewrite (Er _). reflexivity.
Qed.

Lemma det_reserve
  {r1 r2} (Er : Map.Eq r1 r2)
  {t1 t2} (Et : t1 = t2)
  : unshadow_reserve r1 t1 = unshadow_reserve r2 t2.
Proof. unfold unshadow_reserve. destruct (det_bindings Er Et); reflexivity. Qed.



Lemma bound_or_used {acc cant_bind term bound_or_used renamed}
  (E : unshadow_acc acc cant_bind term = Some (bound_or_used, renamed))
  : Map.Reflect (fun x => BoundIn.Term renamed x \/ UsedIn.Term renamed x \/ Map.In cant_bind x) bound_or_used.
Proof.
  generalize dependent renamed. generalize dependent bound_or_used.
  generalize dependent cant_bind. generalize dependent acc. induction term; intros.
  - invert E. split. { intro I. right. right. exact I. }
    intros [B | [U | I]]. { invert B. } { invert U. } exact I.
  - cbn in E. destruct (Map.find_spec acc name) as [name' F | N]; invert E. split.
    + intro I. apply Map.in_overriding_add in I as [-> | I]. { right. left. constructor. } right. right. exact I.
    + intros [B | [U | I]]. { invert B. } { invert U. apply Map.in_overriding_add. left. reflexivity. }
      apply Map.in_overriding_add. right. exact I.
  - cbn in E. destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E. eapply IHterm1 in E1; try eassumption.
    eapply IHterm2 in E2; try eassumption. split.
    + intro I. apply E2 in I as [B | [U | I]].
      * left. apply BoundIn.TApA. exact B.
      * right. left. apply UsedIn.ApA. exact U.
      * apply E1 in I as [B | [U | I]]; [left | right; left | right; right]. { apply BoundIn.TApF. exact B. } 2: { exact I. }
        apply UsedIn.ApF. exact U.
    + intro UI. apply E2. destruct UI as [B | [U | I]].
      * invert B. 2: { left. exact bound_in_argument. } right. right. apply E1. left. exact bound_in_function.
      * invert U. 2: { right. left. exact used_in_argument. } right. right. apply E1. right. left. exact used_in_function.
      * right. right. apply E1. right. right. exact I.
  - rewrite unshadow_for in E. destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    apply IHterm1 in E1. apply IHterm2 in E2. split.
    + intro I. apply E2 in I as [B | [U | I]]. { left. apply BoundIn.TFoB. exact B. }
      * destruct (String.eqb_spec x $ NewNames.new_name cant_bind variable); [| right]; left. { subst. apply BoundIn.TFoV. }
        apply UsedIn.FoB. { exact n. } exact U.
      * apply E1 in I as [B | [U | I]]. { left. apply BoundIn.TFoT. exact B. } { right. left. apply UsedIn.FoT. exact U. }
        apply Map.in_overriding_add in I as [-> | I]. { left. apply BoundIn.TFoV. } right. right. exact I.
    + intro BI. apply E2. destruct BI as [B | [U | I]].
      * invert B; [| | left; exact bound_in_body]; right; right; apply E1. 2: { left. exact bound_in_type. }
        right. right. apply Map.in_overriding_add. left. reflexivity.
      * right. invert U. 2: { left. exact used_in_body. } right. apply E1. right. left. exact used_in_type.
      * right. right. apply E1. right. right. apply Map.in_overriding_add. right. exact I.
  - rewrite unshadow_cas in E. destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct Rename.pattern eqn:R. 2: { discriminate E. } eapply (Rename.pattern_iff $ NewNames.one_to_one_generate _ _) in R.
    destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E; invert E.
    apply IHterm2 in E2. apply IHterm1 in E1. split.
    + intro I. apply E1 in I as [B | [U | I]]. { left. apply BoundIn.TCaB. exact B. } {
        destruct (BoundIn.pattern_spec p x); [| right]; left. { apply BoundIn.TCaP. exact Y. }
        apply UsedIn.CaB. 2: { exact U. } exact N. }
      apply E2 in I as [B | [U | I]]. { left. apply BoundIn.TCaO. exact B. } { right. left. apply UsedIn.CaO. exact U. }
      apply Map.in_overriding_union in I as [I | I]. 2: { right. right. exact I. }
      apply Map.in_space_range in I as [w F]. left. apply BoundIn.TCaP. eapply (Rename.bound_in_pattern R).
      exists w. split. 2: { exact F. } apply BoundIn.pattern_iff. eapply NewNames.in_generate. exists x. exact F.
    + intro BUI. apply E1. destruct BUI as [B | [U | I]].
      * invert B; [| left; exact bound_in_body |]; right; right; apply E2. 2: { left. exact bound_in_another_case. }
        right. right. apply Map.in_overriding_union. left. apply (Rename.bound_in_pattern R) in bound_in_pattern as [w [B F]].
        apply Map.in_space_range. exists w. exact F.
      * right. invert U. { left. exact used_in_body. } right. apply E2. right. left. exact used_in_another_case.
      * right. right. apply E2. right. right. apply Map.in_overriding_union. right. exact I.
Qed.



Lemma wf_patterns_spec_acc acc cant_bind t
  : Reflect.Option (fun '(cant_bind', t') =>
      WellFormed.AllPatternsIn t /\
      WellFormed.AllPatternsIn t' /\
      forall x (U : UsedIn.Term t x), Map.In acc x
    ) $ unshadow_acc acc cant_bind t.
Proof.
  generalize dependent cant_bind. generalize dependent acc. induction t; intros.
  - constructor. split. { constructor. } split. { constructor. } intros. invert U.
  - cbn. destruct (Map.find_spec acc name); constructor.
    + split; intros. { constructor. } split. { constructor. } intros. invert U. eexists. exact Y.
    + intros [cant_bind' t'] [WF [WF' C]]. edestruct C. { constructor. } apply N in H as [].
  - cbn. destruct (IHt1 acc cant_bind) as [[r1 t1'] [WF1 [WF1' IH1]] |]. 2: {
      constructor. intros [cant_bind' t'] [WF [WF' C]]. invert WF. eapply (N (cant_bind', t')).
      split. { exact APf. } split. { exact WF'. } intros. apply C. apply UsedIn.ApF. exact U. }
    destruct (IHt2 acc r1) as [[r2 t2'] [WF2 [WF2' IH2]] |]; constructor.
    + split. { constructor; assumption. } split. { constructor. { exact WF1'. } exact WF2'. }
      intros. invert U; [apply IH1 | apply IH2]; assumption.
    + intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APa. } split. { exact WF'. } intros. apply C. apply UsedIn.ApA. exact U.
  - rewrite unshadow_for.
    destruct (IHt1 acc $ Map.set_add (NewNames.new_name cant_bind variable) cant_bind) as [[r1 t1'] [WF1 [WF1' IH1]] |]. 2: {
      constructor. intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APt. } split. { exact WF'. } intros. apply C. apply UsedIn.FoT. exact U. }
    destruct (IHt2 (Map.overwrite variable (NewNames.new_name cant_bind variable) acc) r1) as [[r2 t2'] [WF2 [WF2' IH2]] |]; constructor.
    + split. { constructor; assumption. } split. { constructor. { exact WF1'. } exact WF2'. }
      intros. invert U. { apply IH1. exact used_in_type. }
      apply IH2 in used_in_body. apply Map.in_overriding_add in used_in_body as [-> | I]. 2: { exact I. }
      contradiction not_shadowed. reflexivity.
    + intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APb. } split. { exact WF'. } intros. apply Map.in_overriding_add.
      destruct (String.eqb_spec x variable); [left | right]. { assumption. } apply C. apply UsedIn.FoB; assumption.
  - rewrite unshadow_cas. destruct (IHt2 acc $ Map.set_union (Map.range $ NewNames.generate cant_bind $ BoundIn.pattern pattern)
      cant_bind) as [[r2 t2'] [WF2 [WF2' IH2]] |]. 2: {
      constructor. intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APo. } split. { exact WF'. } intros. apply C. apply UsedIn.CaO. exact U. }
    destruct Rename.pattern eqn:R. 2: {
      constructor. intros [cant_bind' t'] [WF [WF' C]]. invert WF. eassert (RC : Rename.CompatiblePattern _ _). 2: {
        apply Rename.pattern_iff_compatible in RC as [O2O [renamed R']].
        apply (Rename.pattern_iff O2O) in R'. rewrite R' in R. discriminate R. }
      invert WFp; constructor. { apply NewNames.one_to_one_generate. } {
        apply NewNames.in_generate. apply Map.in_singleton. reflexivity. }
      invert move_or_reference_well_formed; constructor; (split; [apply NewNames.one_to_one_generate |]);
      (split; [exact strict_well_formed |]); intros k [] F; apply Map.find_domain;
      apply NewNames.in_generate; cbn; exists tt; exact F. }
    apply (Rename.pattern_iff $ NewNames.one_to_one_generate _ _) in R.
    eassert (RC : Rename.CompatiblePattern _ _). { apply Rename.pattern_iff_compatible. do 2 eexists. exact R. }
    destruct (IHt1 (Map.bulk_overwrite (NewNames.generate cant_bind $ BoundIn.pattern pattern) acc)
      r2) as [[r1 t1'] [WF1 [WF1' IH1]] |]; constructor.
    + constructor. { constructor; try assumption. invert RC; constructor. invert C; constructor; apply CS. }
      split. { constructor. 2: { exact WF1'. } 2: { exact WF2'. } invert R; constructor.
        invert rename_move_or_reference; constructor; eapply Rename.wf_strict; exact rename_strict. }
      intros z U. invert U. 2: { apply IH2. exact used_in_another_case. } apply IH1 in used_in_body.
      apply Map.in_overriding_union in used_in_body as [I | I]. 2: { exact I. }
      apply NewNames.in_generate in I. apply BoundIn.pattern_iff in I. apply not_shadowed in I as [].
    + intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APb. } split. { exact WF'. } intros.
      apply Map.in_overriding_union. destruct (BoundIn.pattern_spec pattern x); [left | right].
      * apply NewNames.in_generate. apply BoundIn.pattern_iff. exact Y.
      * apply C. apply UsedIn.CaB; assumption.
Qed.

Lemma wf_patterns_spec_bindings cant_bind t
  : Reflect.Option (fun '(cant_bind', t') =>
      WellFormed.AllPatternsIn t /\ WellFormed.AllPatternsIn t'
    ) $ unshadow_reserve_bindings cant_bind t.
Proof.
  unfold unshadow_reserve. unfold unshadow_reserve_bindings.
  destruct (wf_patterns_spec_acc (Map.to_self $ UsedIn.term t)
    (Map.set_union cant_bind $ UsedIn.term t) t) as [[domain' renamed] |]; cbn; constructor.
  - destruct Y as [WF [WF' AU]]. split. { exact WF. } exact WF'.
  - intros [cant_bind' t'] [WF WF']. apply (N (cant_bind', t')). split. { exact WF. }
    split. { exact WF'. } intros. apply Map.in_to_self. apply UsedIn.term_iff. exact U.
Qed.

Lemma wf_patterns_spec domain t
  : Reflect.Option (fun t' =>
      WellFormed.AllPatternsIn t /\ WellFormed.AllPatternsIn t'
    ) $ unshadow_reserve domain t.
Proof.
  unfold unshadow_reserve. destruct (wf_patterns_spec_bindings domain t) as [[cant_bind' t'] |];
  constructor. { exact Y. } intro. exact (N (Map.empty, x)).
Qed.



Lemma disjoint_used {acc cant_bind term cant_bind' renamed}
  (E : unshadow_acc acc cant_bind term = Some (cant_bind', renamed))
  {y} (I : Map.In cant_bind y) (U : UsedIn.Term renamed y)
  : exists x, Map.Find acc x y.
Proof.
  generalize dependent y. generalize dependent renamed. generalize dependent cant_bind'.
  generalize dependent cant_bind. generalize dependent acc. induction term; intros.
  - invert E. invert U.
  - cbn in E. destruct (Map.find_spec acc name); invert E. invert U. eexists. exact Y.
  - cbn in E. destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    invert U. { eapply IHterm1. { exact E1. } { exact I. } exact used_in_function. }
    eapply IHterm2. { exact E2. } 2: { exact used_in_argument. }
    eapply bound_or_used. { exact E1. } right. right. exact I.
  - rewrite unshadow_for in E. destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    invert U. { eapply IHterm1. { exact E1. } 2: { exact used_in_type. } apply Map.in_overriding_add. right. exact I. }
    eapply IHterm2 in E2 as [x IH2]. 3: { exact used_in_body. }
    + apply Map.find_overriding_add in IH2 as [[-> ->] | [N F]]. { contradiction not_shadowed. reflexivity. } eexists. exact F.
    + eapply bound_or_used. { exact E1. } right. right. apply Map.in_overriding_add. right. exact I.
  - rewrite unshadow_cas in E. destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct Rename.pattern eqn:R. 2: { discriminate E. } apply (Rename.pattern_iff $ NewNames.one_to_one_generate _ _) in R.
    destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E; invert E.
    invert U. 2: { eapply IHterm2. { exact E2. } 2: { exact used_in_another_case. } apply Map.in_overriding_union. right. exact I. }
    eapply IHterm1 in E1 as [z IH1]. 3: { exact used_in_body. }
    + apply Map.bulk_overwrite_bulk_overwrite in IH1 as [F | [N F]]. 2: { eexists. exact F. }
      eassert (I' : Map.In _ _). { eexists. exact F. } apply NewNames.in_generate in I'. apply BoundIn.pattern_iff in I' as B.
      contradiction not_shadowed. eapply Rename.bound_in_pattern. { exact R. } eexists. split. { exact B. } exact F.
    + eapply bound_or_used. { exact E2. } right. right. apply Map.in_overriding_union. right. exact I.
Qed.

Lemma disjoint_bound {acc cant_bind term cant_bind' renamed}
  (E : unshadow_acc acc cant_bind term = Some (cant_bind', renamed))
  {x} (I : Map.In cant_bind x) (B : BoundIn.Term renamed x)
  : False.
Proof.
  generalize dependent x. generalize dependent renamed. generalize dependent cant_bind'.
  generalize dependent cant_bind. generalize dependent acc. induction term; intros.
  - invert E. invert B.
  - cbn in E. destruct (Map.find_spec acc name); invert E. invert B.
  - cbn in E. destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    invert B. { eapply IHterm1. { exact E1. } { exact I. } exact bound_in_function. }
    eapply IHterm2. { exact E2. } 2: { exact bound_in_argument. }
    eapply bound_or_used. { exact E1. } right. right. exact I.
  - rewrite unshadow_for in E. destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E. invert B.
    + eapply NewNames.not_in_new_name in I as [].
    + eapply IHterm1. { exact E1. } 2: { exact bound_in_type. } apply Map.in_overriding_add. right. exact I.
    + eapply IHterm2 in E2 as []. 2: { exact bound_in_body. }
      eapply bound_or_used. { exact E1. } right. right. apply Map.in_overriding_add. right. exact I.
  - rewrite unshadow_cas in E. destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct Rename.pattern eqn:R. 2: { discriminate E. } apply (Rename.pattern_iff $ NewNames.one_to_one_generate _ _) in R.
    destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E; invert E. invert B.
    + apply (Rename.bound_in_pattern R) in bound_in_pattern as [z [B F]].
      eapply NewNames.not_in_generate. { exact I. } exists z. exact F.
    + eapply IHterm1 in E1 as []. 2: { exact bound_in_body. }
      eapply bound_or_used. { exact E2. } right. right. apply Map.in_overriding_union. right. exact I.
    + eapply IHterm2. { exact E2. } 2: { exact bound_in_another_case. } apply Map.in_overriding_union. right. exact I.
Qed.

Lemma used_cant_bind {acc cant_bind term cant_bind' renamed}
  (E : unshadow_acc acc cant_bind term = Some (cant_bind', renamed))
  {x} (U : UsedIn.Term renamed x)
  : Map.In cant_bind' x.
Proof.
  generalize dependent x. generalize dependent renamed. generalize dependent cant_bind'.
  generalize dependent cant_bind. generalize dependent acc. induction term; intros; cbn in *.
  - invert E. invert U.
  - destruct (Map.find_spec acc name); invert E. invert U. apply Map.in_overriding_add. left. reflexivity.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E. invert U. 2: { eapply IHterm2; eassumption. }
    eapply IHterm1 in E1; try eassumption. eapply bound_or_used; try eassumption. right. right. exact E1.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E. invert U. 2: { eapply IHterm2. { exact E2. } exact used_in_body. }
    eapply IHterm1 in E1; try eassumption. eapply bound_or_used; try eassumption. right. right. exact E1.
  - destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct Rename.pattern eqn:R. 2: { discriminate E. } apply (Rename.pattern_iff $ NewNames.one_to_one_generate _ _) in R.
    destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E; invert E. invert U. { eapply IHterm1. { exact E1. } exact used_in_body. }
    eapply IHterm2 in E2; try eassumption. eapply bound_or_used; try eassumption. right. right. exact E2.
Qed.



(* This relation asks whether another specified relation holds of any root and its children, anywhere in the tree.
 * There are two versions: lateral, in which all roots are tested symmetrically, and
 * non-lateral, in which a relation may depend on differing contexts between children (specifically, `For` and `Cas` nodes). *)
Inductive Anywhere (Lateral : Prop)
  (P : forall (bindings : String.string -> Prop) (aux deep : Term.term), Prop)
  : Term.term -> Prop :=
  | APAF (lateral : Lateral) {function argument} (here : P (fun _ => False) function argument)
      : Anywhere Lateral P $ Term.App function argument
  | APAA (lateral : Lateral) {function argument} (here : P (fun _ => False) argument function)
      : Anywhere Lateral P $ Term.App function argument
  | APFT {variable type body} (here : P (eq variable) type body)
      : Anywhere Lateral P $ Term.For variable type body
  | APFB (lateral : Lateral) {variable type body} (here : P (eq variable) body type)
      : Anywhere Lateral P $ Term.For variable type body
  | APCB (lateral : Lateral) {pattern body_if_match other_cases} (here : P (BoundIn.Pattern pattern) body_if_match other_cases)
      : Anywhere Lateral P $ Term.Cas pattern body_if_match other_cases
  | APCO {pattern body_if_match other_cases} (here : P (BoundIn.Pattern pattern) other_cases body_if_match)
      : Anywhere Lateral P $ Term.Cas pattern body_if_match other_cases
  | ARAF {function} (R : Anywhere Lateral P function) argument
      : Anywhere Lateral P $ Term.App function argument
  | ARAA {argument} (R : Anywhere Lateral P argument) function
      : Anywhere Lateral P $ Term.App function argument
  | ARFT {type} (R : Anywhere Lateral P type) variable body
      : Anywhere Lateral P $ Term.For variable type body
  | ARFB {body} (R : Anywhere Lateral P body) variable type
      : Anywhere Lateral P $ Term.For variable type body
  | ARCB {body_if_match} (R : Anywhere Lateral P body_if_match) pattern other_cases
      : Anywhere Lateral P $ Term.Cas pattern body_if_match other_cases
  | ARCO {other_cases} (R : Anywhere Lateral P other_cases) pattern body_if_match
      : Anywhere Lateral P $ Term.Cas pattern body_if_match other_cases
  .
Arguments Anywhere Lateral P t.

(* If a variable is bound at the root of a subtree and then bound again in that subtree: *)
Definition HasShadow := Anywhere True $ fun Bound child _ => exists x, Bound x /\ BoundIn.Term child x.

(* If a variable is bound in one subtree of the AST and used in an adjacent subtree: *)
(* (name from Einstein's "spooky action at a distance" remark) *)
Definition Spooky := Anywhere True $ fun _ child1 child2 => exists x, UsedIn.Term child1 x /\ BoundIn.Term child2 x.

(* If a variable is bound in both children, separately: *)
Definition Parallel := Anywhere True $ fun _ child1 child2 => exists x, BoundIn.Term child1 x /\ BoundIn.Term child2 x.

(* If a variable is bound and then used immediately in a child,
 * but the wrong child (e.g. `forall x : x, ...` or `case x => { ... } else x`): *)
Definition LateralScope := Anywhere False $ fun Bound cant_use_bindings _ => exists x, Bound x /\ UsedIn.Term cant_use_bindings x.



Definition WellFormedNeg t : Prop := WellFormed.AllPatternsIn t /\ (~HasShadow t) /\ (~Spooky t) /\ (~Parallel t) /\ (~LateralScope t).
Arguments WellFormedNeg t/.

Definition WellFormedNegInAcc (cant_bind context : Map.set) t : Prop :=
  WellFormedNeg t /\ forall x, (
    (forall (B : BoundIn.Term t x) (I : Map.In cant_bind x), False) /\
    (forall (U : UsedIn.Term t x), Map.In context x)).
Arguments WellFormedNegInAcc cant_bind context t/.

Definition WellFormedNegIn context := WellFormedNegInAcc context context.
Arguments WellFormedNegIn context t/.

Definition bind {A B C} (f : A -> B -> option C) (x : option (A * B)) :=
  match x with None => None | Some (bound, used) => f bound used end.
Arguments bind {A B C} f x/.

Fixpoint well_formed_in_acc cant_bind context t :=
  match t with
  | Term.Ctr _ => Some (Map.empty, Map.empty)
  | Term.Var name _ => if Map.in_ context name then Some (Map.empty, Map.singleton name tt) else None
  | Term.App function argument =>
      bind (fun bound_in_function used_in_function =>
        bind (fun bound_in_argument used_in_argument =>
          if Map.disjoint bound_in_function bound_in_argument then
            if Map.disjoint bound_in_function used_in_argument then
              if Map.disjoint bound_in_argument used_in_function then Some (
                Map.set_union bound_in_function bound_in_argument,
                Map.set_union used_in_function used_in_argument)
              else None
            else None
          else None
        ) (well_formed_in_acc cant_bind context argument)
      ) (well_formed_in_acc cant_bind context function)
  | Term.For variable type body =>
      bind (fun bound_in_type used_in_type =>
        let bound_or_used_in_body_without_bindings := Map.set_union cant_bind $ Map.set_union bound_in_type used_in_type in
        if Map.in_ bound_or_used_in_body_without_bindings variable then None else
        let bound_or_used_in_body := Map.set_add variable bound_or_used_in_body_without_bindings in
        let context_in_body := Map.set_add variable context in
        bind (fun bound_in_body used_in_body =>
          if Map.disjoint bound_in_type bound_in_body then
            if Map.disjoint bound_in_type used_in_body then
              if Map.disjoint bound_in_body used_in_type then Some (
                Map.set_add variable $ Map.set_union bound_in_type bound_in_body,
                Map.set_union used_in_type $ Map.remove variable used_in_body)
              else None
            else None
          else None
        ) (well_formed_in_acc bound_or_used_in_body context_in_body body)
      ) (well_formed_in_acc cant_bind context type)
  | Term.Cas pattern body_if_match other_cases =>
      bind (fun bound_in_other_cases used_in_other_cases =>
        let bound_or_used_in_body_without_bindings := Map.set_union cant_bind $ Map.set_union bound_in_other_cases used_in_other_cases in
        if WellFormed.pattern pattern then
          let bound_in_pattern := BoundIn.pattern pattern in
          if Map.disjoint bound_or_used_in_body_without_bindings bound_in_pattern then
            let bound_or_used_in_body_if_match := Map.set_union bound_in_pattern bound_or_used_in_body_without_bindings in
            let context_in_body_if_match := Map.set_union bound_in_pattern context in
            bind (fun bound_in_body_if_match used_in_body_if_match =>
              if Map.disjoint bound_in_other_cases bound_in_body_if_match then
                if Map.disjoint bound_in_other_cases used_in_body_if_match then
                  if Map.disjoint bound_in_body_if_match used_in_other_cases then Some (
                    Map.set_union bound_in_pattern $ Map.set_union bound_in_other_cases bound_in_body_if_match,
                    Map.set_union used_in_other_cases $ Map.minus used_in_body_if_match bound_in_pattern)
                  else None
                else None
              else None
            ) (well_formed_in_acc bound_or_used_in_body_if_match context_in_body_if_match body_if_match)
          else None
        else None
      ) (well_formed_in_acc cant_bind context other_cases)
  end.

Definition well_formed_in context t :=
  match well_formed_in_acc context context t with
  | None => false
  | Some _ => true
  end.

Lemma bound_used {cant_bind context t bound used} (E : well_formed_in_acc cant_bind context t = Some (bound, used))
  : Map.Reflect (BoundIn.Term t) bound /\ Map.Reflect (UsedIn.Term t) used.
Proof.
  generalize dependent used. generalize dependent bound. generalize dependent context. generalize dependent cant_bind.
  induction t; intros; cbn in *.
  - invert E. split; intro x.
    + split. { intro I. apply Map.empty_empty in I as []. } intro B. invert B.
    + split. { intro I. apply Map.empty_empty in I as []. } intro U. invert U.
  - destruct (Map.in_spec context name); invert E. split; intro x.
    + split. { intro I. apply Map.empty_empty in I as []. } intro B. invert B.
    + split. { intro I. apply Map.in_singleton in I as ->. constructor. } intro U. invert U. apply Map.in_singleton. reflexivity.
  - destruct well_formed_in_acc as [[b1 u1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct well_formed_in_acc as [[b2 u2] |] eqn:E2 in E. 2: { discriminate E. }
    specialize (IHt1 _ _ _ _ E1) as [B1 U1]. specialize (IHt2 _ _ _ _ E2) as [B2 U2].
    destruct Map.disjoint eqn:D1 in E. 2: { discriminate E. }
    destruct Map.disjoint eqn:D2 in E. 2: { discriminate E. }
    destruct Map.disjoint eqn:D3 in E; invert E. split; intro x; rewrite Map.in_overriding_union.
    + split.
      * intros [I | I]; [apply BoundIn.TApF | apply BoundIn.TApA]; [apply B1 | apply B2]; exact I.
      * intro B. invert B; [left | right]; [apply B1 | apply B2]; assumption.
    + split.
      * intros [I | I]; [apply UsedIn.ApF | apply UsedIn.ApA]; [apply U1 | apply U2]; exact I.
      * intro U. invert U; [left | right]; [apply U1 | apply U2]; assumption.
  - destruct well_formed_in_acc as [[b1 u1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct (Map.in_spec (Map.overriding_union cant_bind $ Map.overriding_union b1 u1) variable). { discriminate E. }
    destruct well_formed_in_acc as [[b2 u2] |] eqn:E2 in E. 2: { discriminate E. }
    specialize (IHt1 _ _ _ _ E1) as [B1 U1]. specialize (IHt2 _ _ _ _ E2) as [B2 U2].
    destruct Map.disjoint eqn:D1 in E. 2: { discriminate E. }
    destruct Map.disjoint eqn:D2 in E. 2: { discriminate E. }
    destruct Map.disjoint eqn:D3 in E; invert E. split; intro x.
    + rewrite Map.in_overriding_add. rewrite Map.in_overriding_union. split.
      * intros [-> | [I | I]]; [apply BoundIn.TFoV | apply BoundIn.TFoT | apply BoundIn.TFoB]; [apply B1 | apply B2]; exact I.
      * intro B. invert B; [left; reflexivity | |]; right; [left | right]; [apply B1 | apply B2]; assumption.
    + rewrite Map.in_overriding_union. rewrite (Map.in_remove_if_present $ Map.remove_if_present_remove _ _). split.
      * intros [I | [Nx I]]; [apply UsedIn.FoT | apply UsedIn.FoB]; [apply U1 | exact Nx | apply U2]; exact I.
      * intro U. invert U; [left | right]; [| split; [exact not_shadowed |]]; [apply U1 | apply U2]; assumption.
  - destruct well_formed_in_acc as [[b2 u2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct (WellFormed.pattern_spec pattern). 2: { discriminate E. } destruct Map.disjoint eqn:D1 in E. 2: { discriminate E. }
    destruct well_formed_in_acc as [[b1 u1] |] eqn:E1 in E. 2: { discriminate E. }
    specialize (IHt1 _ _ _ _ E1) as [B1 U1]. specialize (IHt2 _ _ _ _ E2) as [B2 U2].
    destruct Map.disjoint eqn:D2 in E. 2: { discriminate E. }
    destruct Map.disjoint eqn:D3 in E. 2: { discriminate E. }
    destruct Map.disjoint eqn:D4 in E; invert E. split; intro x; repeat rewrite Map.in_overriding_union.
    + split.
      * intros [I | [I | I]]; [apply BoundIn.TCaP; apply BoundIn.pattern_iff; exact I | |];
        [apply BoundIn.TCaO | apply BoundIn.TCaB]; [apply B2 | apply B1]; try exact I.
      * intro B. invert B; [left; apply BoundIn.pattern_iff; exact bound_in_pattern | |];
        right; [right | left]; [apply B1 | apply B2]; assumption.
    + rewrite Map.in_minus. split.
      * intros [I | [I N]]; [apply UsedIn.CaO | apply UsedIn.CaB]; [apply U2 | | apply U1]; try exact I.
        intro B. apply N. apply BoundIn.pattern_iff. exact B.
      * intro U. invert U; [right | left]; [split |]; [apply U1 | | apply U2]; try assumption.
        intro B. apply not_shadowed. apply BoundIn.pattern_iff. exact B.
Qed.

Lemma well_formed_in_acc_spec
  {t context} (no_free_vars : forall x (U : UsedIn.Term t x), Map.In context x)
  {cant_bind} (bound_or_used_context : forall x (I : Map.In context x), Map.In cant_bind x)
  : Reflect.Option (fun _ => WellFormedNegInAcc cant_bind context t) $
    well_formed_in_acc cant_bind context t.
Proof.
  generalize dependent cant_bind. generalize dependent context. induction t; intros; cbn in *.
  - constructor. split. { split. { constructor. } repeat split; intro C; invert C. } split; intros. { invert B. } invert U.
  - destruct (Map.in_spec context name); constructor.
    + split. { split. { constructor. } repeat split; intro C; invert C. } split; intros. { invert B. } invert U. exact Y.
    + eintros _ [_ [_ C]]. apply N in C as []. constructor.
  - eassert (no_free_vars_1 : _); [| specialize (IHt1 context no_free_vars_1 cant_bind bound_or_used_context)]. {
      intros. apply no_free_vars. apply UsedIn.ApF. exact U. }
    destruct well_formed_in_acc as [[b1 u1] |] eqn:E1 in IHt1; rewrite E1; invert IHt1. 2: {
      constructor. intros pair [[AP [NH [NS [NP NL]]]] C]. apply (N pair). split. 2: { intro x. specialize (C x) as [C1 C2].
        split; intros; [apply C1 | apply C2]. { apply BoundIn.TApF. exact B. } { exact I. } apply UsedIn.ApF. exact U. }
      split. { invert AP. exact APf. } repeat split; intro; [apply NH | apply NS | apply NP | apply NL]; apply ARAF; assumption. }
    eassert (no_free_vars_2 : _); [| specialize (IHt2 context no_free_vars_2 cant_bind bound_or_used_context)]. {
      intros. apply no_free_vars. apply UsedIn.ApA. exact U. }
    destruct well_formed_in_acc as [[b2 u2] |] eqn:E2 in IHt2; rewrite E2; invert IHt2. 2: {
      constructor. intros pair [[AP [NH [NS [NP NL]]]] C]. apply (N pair). split. 2: { intro x. specialize (C x) as [C1 C2].
        split; intros; [apply C1 | apply C2]. { apply BoundIn.TApA. exact B. } { exact I. } apply UsedIn.ApA. exact U. }
      split. { invert AP. exact APa. } repeat split; intro; [apply NH | apply NS | apply NP | apply NL]; apply ARAA; assumption. }
    destruct (bound_used E1) as [B1 U1]. destruct (bound_used E2) as [B2 U2]. destruct (Map.disjoint_spec b1 b2). 2: {
      constructor. intros _ [[_ [_ [_ [C _]]]] _]. apply C. apply APAF. { constructor. }
      apply Map.not_disjoint_exists in N as [x [C1 C2]]. exists x. split; [apply B1 | apply B2]; assumption. }
    destruct (Map.disjoint_spec b1 u2). 2: {
      constructor. intros _ [[_ [_ [C [_ _]]]] _]. apply C. apply APAA. { constructor. }
      apply Map.not_disjoint_exists in N as [x [C1 C2]]. exists x. split; [apply U2 | apply B1]; assumption. }
    destruct (Map.disjoint_spec b2 u1); constructor. 2: {
      intros _ [[_ [_ [C [_ _]]]] _]. apply C. apply APAF. { constructor. }
      apply Map.not_disjoint_exists in N as [x [C1 C2]]. exists x. split; [apply U1 | apply B2]; assumption. }
    split.
    + split. { constructor. { apply Y. } apply Y0. } repeat split; intro C; invert C; try solve [destruct here as [_ [[]]]];
      try solve [apply Y in R as []]; try solve [apply Y0 in R as []].
      * destruct here as [x [U1' B2']]. apply (Y3 x); [apply B2 | apply U1]; assumption.
      * destruct here as [x [U2' B1']]. apply (Y2 x); [apply B1 | apply U2]; assumption.
      * destruct here as [x [B1' B2']]. apply (Y1 x); [apply B1 | apply B2]; assumption.
      * destruct here as [x [B2' B1']]. apply (Y1 x); [apply B1 | apply B2]; assumption.
    + destruct Y as [_ H1]. destruct Y0 as [_ H2]. split; intros.
      * invert B; [eapply H1 | eapply H2]; eassumption.
      * invert U; [apply H1 | apply H2]; assumption.
  - eassert (no_free_vars_1 : _); [| specialize (IHt1 context no_free_vars_1 cant_bind bound_or_used_context)]. {
      intros. apply no_free_vars. apply UsedIn.FoT. exact U. }
    destruct well_formed_in_acc as [[b1 u1] |] eqn:E1 in IHt1; rewrite E1; invert IHt1. 2: {
      constructor. intros pair [[AP [NH [NS [NP NL]]]] C]. apply (N pair). split. 2: { intro x. specialize (C x) as [C1 C2].
        split; intros; [apply C1 | apply C2]. { apply BoundIn.TFoT. exact B. } { exact I. } apply UsedIn.FoT. exact U. }
      split. { invert AP. exact APt. } repeat split; intro;
      [apply NH | apply NS | apply NP | apply NL]; apply ARFT; assumption. } destruct (bound_used E1) as [B1 U1].
    destruct (Map.in_spec (Map.overriding_union cant_bind $ Map.overriding_union b1 u1) variable). { constructor.
      intros _ [[AP [NH [NS [NP NL]]]] C]. apply Map.in_overriding_union in Y0 as [I | I]. { eapply C. { apply BoundIn.TFoV. } exact I. }
      apply Map.in_overriding_union in I as [I | I]; [apply B1 in I as B | apply U1 in I as U].
      * apply NH. apply APFT. exists variable. split. { reflexivity. } exact B.
      * apply NL. apply APFT. exists variable. split. { reflexivity. } exact U. }
    eassert (no_free_vars_2 : _); [| specialize (IHt2 (Map.overriding_add variable tt context)
      no_free_vars_2 (Map.overriding_add variable tt $ Map.overriding_union cant_bind $ Map.overriding_union b1 u1))]. {
      intros. apply Map.in_overriding_add. destruct (String.eqb_spec x variable); [left | right]. { exact e. }
      apply no_free_vars. apply UsedIn.FoB. { exact n. } exact U. }
    eassert (bound_or_used_context' : _); [| specialize (IHt2 bound_or_used_context')]. {
      intro x. repeat rewrite Map.in_overriding_add. destruct (String.eqb_spec x variable); [left | right]. { exact e. }
      destruct I as [E | I]. { apply n in E as []. } repeat rewrite Map.in_overriding_union. left. apply bound_or_used_context. exact I. }
    destruct well_formed_in_acc as [[b2 u2] |] eqn:E2 in IHt2; rewrite E2 in *; invert IHt2. 2: {
      constructor. intros pair [[AP [NH [NS [NP NL]]]] C]. apply (N0 pair). split. {
        split. { invert AP. exact APb. } repeat split; intro NA; [apply NH | apply NS | apply NP | apply NL]; apply ARFB; exact NA. }
      intro x. specialize (C x) as [C1 C2]. split.
      * intros B I. apply Map.in_overriding_add in I as [-> | I]. {
          apply NH. apply APFB. { constructor. } exists variable. split. { reflexivity. } exact B. }
        apply Map.in_overriding_union in I as [I | I]. { eapply C1. 2: { exact I. } apply BoundIn.TFoB. exact B. }
        apply Map.in_overriding_union in I as [I | I]. { apply B1 in I. eapply NP. apply APFT. exists x. split; assumption. }
        apply U1 in I. apply NS. apply APFT. exists x. split. { exact I. } exact B.
      * intro U. apply Map.in_overriding_add. destruct (String.eqb_spec x variable); [left | right]. { exact e. }
        apply C2. apply UsedIn.FoB. { exact n. } exact U. } destruct (bound_used E2) as [B2 U2].
    destruct (Map.disjoint_spec b1 b2). 2: {
      constructor. intros _ [[_ [_ [_ [C _]]]] _]. apply C. apply APFT.
      apply Map.not_disjoint_exists in N0 as [x [C1 C2]]. exists x. split; [apply B1 | apply B2]; assumption. }
    destruct (Map.disjoint_spec b1 u2). 2: {
      constructor. intros _ [[_ [_ [C [_ _]]]] _]. apply C. apply APFB. { constructor. }
      apply Map.not_disjoint_exists in N0 as [x [C1 C2]]. exists x. split; [apply U2 | apply B1]; assumption. }
    destruct (Map.disjoint_spec b2 u1); constructor. 2: {
      intros _ [[_ [_ [C [_ _]]]] _]. apply C. apply APFT.
      apply Map.not_disjoint_exists in N0 as [x [C1 C2]]. exists x. split; [apply U1 | apply B2]; assumption. }
    split.
    + split. { constructor. { apply Y. } apply Y0. }
      repeat split; intro C; invert C; try solve [apply Y in R as []]; try solve [apply Y0 in R as []];
      destruct Y as [[NH1 [NS1 [NP1 NL1]]] C1]; destruct Y0 as [[NH2 [NS2 [NP2 NL2]]] C2].
      * destruct here as [x [<- B]]. apply N. apply Map.in_overriding_union. right.
        apply Map.in_overriding_union. left. apply B1. exact B.
      * destruct here as [x [<- B]]. eapply C2. { exact B. } apply Map.in_overriding_add. left. reflexivity.
      * destruct here as [x [U B]]. eapply (Y3 x); [apply B2 | apply U1]; assumption.
      * destruct here as [x [U B]]. eapply (Y2 x); [apply B1 | apply U2]; assumption.
      * destruct here as [x [B1' B2']]. eapply (Y1 x); [apply B1 | apply B2]; assumption.
      * destruct here as [x [B2' B1']]. eapply (Y1 x); [apply B1 | apply B2]; assumption.
      * destruct here as [x [<- U]]. apply N. apply Map.in_overriding_union. right.
        apply Map.in_overriding_union. right. apply U1. exact U.
      * destruct lateral as [].
    + destruct Y as [[NH1 [NS1 [NP1 NL1]]] C1]. destruct Y0 as [[NH2 [NS2 [NP2 NL2]]] C2]. split; intros.
      * invert B. { apply N. apply Map.in_overriding_union. left. exact I. } { apply (C1 x); assumption. }
        apply (C2 x). { exact bound_in_body. } apply Map.in_overriding_add. right. apply Map.in_overriding_union. left. exact I.
      * invert U. { apply no_free_vars_1. exact used_in_type. } apply no_free_vars_2 in used_in_body.
        apply Map.in_overriding_add in used_in_body as [E | U]. { apply not_shadowed in E as []. } exact U.
  - eassert (no_free_vars_2 : _); [| specialize (IHt2 context no_free_vars_2 cant_bind bound_or_used_context)]. {
      intros. apply no_free_vars. apply UsedIn.CaO. exact U. }
    destruct well_formed_in_acc as [[b2 u2] |] eqn:E2 in IHt2; rewrite E2; invert IHt2. 2: {
      constructor. intros pair [[AP [NH [NS [NP NL]]]] C]. apply (N pair). split. 2: { intro x. specialize (C x) as [C1 C2].
        split; intros; [apply C1 | apply C2]. { apply BoundIn.TCaO. exact B. } { exact I. } apply UsedIn.CaO. exact U. }
      split. { invert AP. exact APo. }
      repeat split; intro; [apply NH | apply NS | apply NP | apply NL]; apply ARCO; assumption. } destruct (bound_used E2) as [B2 U2].
    destruct (WellFormed.pattern_spec pattern). 2: { constructor. intros _ [[AP [NH [NS [NP NL]]]] C]. invert AP. apply N in WFp as []. }
    destruct (Map.disjoint_spec (Map.overriding_union cant_bind $ Map.overriding_union b2 u2) $ BoundIn.pattern pattern). 2: {
      constructor. intros _ [[AP [NH [NS [NP NL]]]] C]. apply N. intros x I B. apply BoundIn.pattern_iff in B.
      apply Map.in_overriding_union in I as [I | I]. { apply (C x). 2: { exact I. } apply BoundIn.TCaP. exact B. }
      apply Map.in_overriding_union in I as [I | I].
      * apply NH. apply APCO. exists x. split. { exact B. } apply B2. exact I.
      * apply NL. apply APCO. exists x. split. { exact B. } apply U2. exact I. }
    eassert (no_free_vars_1 : _); [| specialize (IHt1 (Map.overriding_union (BoundIn.pattern pattern) context)
      no_free_vars_1 (Map.overriding_union (BoundIn.pattern pattern) $ Map.overriding_union cant_bind $ Map.overriding_union b2 u2))]. {
      intros. apply Map.in_overriding_union. destruct (BoundIn.pattern_spec pattern x). { left. apply BoundIn.pattern_iff. exact Y2. }
      right. apply no_free_vars. apply UsedIn.CaB. { exact N. } exact U. }
    eassert (bound_or_used_context' : _); [| specialize (IHt1 bound_or_used_context')]. {
      intro x. repeat rewrite Map.in_overriding_union. intros [I | I]; [left | right]. { exact I. }
      left. apply bound_or_used_context. exact I. }
    destruct well_formed_in_acc as [[b1 u1] |] eqn:E1 in IHt1; rewrite E1 in *; invert IHt1. 2: {
      constructor. intros pair [[AP [NH [NS [NP NL]]]] C]. apply (N pair). split. {
        split. { invert AP. exact APb. } repeat split; intro NA; [apply NH | apply NS | apply NP | apply NL]; apply ARCB; exact NA. }
      intro x. specialize (C x) as [C1 C2]. split.
      * intros B I. apply Map.in_overriding_union in I as [I | I]. {
          apply NH. apply APCB. { constructor. } exists x. split. { apply BoundIn.pattern_iff. exact I. } exact B. }
        apply Map.in_overriding_union in I as [I | I]. { eapply C1. 2: { exact I. } apply BoundIn.TCaB. exact B. }
        apply Map.in_overriding_union in I as [I | I]. { apply B2 in I. eapply NP. apply APCO. exists x. split; assumption. }
        apply U2 in I. apply NS. apply APCO. exists x. split. { exact I. } exact B.
      * intro U. apply Map.in_overriding_union. destruct (BoundIn.pattern_spec pattern x). { left. apply BoundIn.pattern_iff. exact Y2. }
        right. apply C2. apply UsedIn.CaB. { exact N0. } exact U. } destruct (bound_used E1) as [B1 U1].
    destruct (Map.disjoint_spec b2 b1). 2: {
      constructor. intros _ [[_ [_ [_ [C _]]]] _]. apply C. apply APCO.
      apply Map.not_disjoint_exists in N as [x [C1 C2]]. exists x. split; [apply B2 | apply B1]; assumption. }
    destruct (Map.disjoint_spec b2 u1). 2: {
      constructor. intros _ [[_ [_ [C [_ _]]]] _]. apply C. apply APCB. { constructor. }
      apply Map.not_disjoint_exists in N as [x [C1 C2]]. exists x. split; [apply U1 | apply B2]; assumption. }
    destruct (Map.disjoint_spec b1 u2); constructor. 2: {
      intros _ [[_ [_ [C [_ _]]]] _]. apply C. apply APCO.
      apply Map.not_disjoint_exists in N as [x [C1 C2]]. exists x. split; [apply U2 | apply B1]; assumption. }
    split.
    + split. { constructor. { exact Y0. } { apply Y2. } apply Y. }
      repeat split; intro C; invert C; try solve [apply Y in R as []]; try solve [apply Y2 in R as []];
      destruct Y as [[NH1 [NS1 [NP1 NL1]]] C1]; destruct Y2 as [[NH2 [NS2 [NP2 NL2]]] C2].
      * destruct here as [x [Bp B]]. eapply C2. { exact B. } apply Map.in_overriding_union. left. apply BoundIn.pattern_iff. exact Bp.
      * destruct here as [x [Bp B]]. apply (Y1 x). 2: { apply BoundIn.pattern_iff. exact Bp. }
        apply Map.in_overriding_union. right. apply Map.in_overriding_union. left. apply B2. exact B.
      * destruct here as [x [U B]]. eapply (Y4 x); [apply B2 | apply U1]; assumption.
      * destruct here as [x [U B]]. eapply (Y5 x); [apply B1 | apply U2]; assumption.
      * destruct here as [x [B1' B2']]. eapply (Y3 x); [apply B2 | apply B1]; assumption.
      * destruct here as [x [B2' B1']]. eapply (Y3 x); [apply B2 | apply B1]; assumption.
      * destruct lateral as [].
      * destruct here as [x [Bp U]]. apply (Y1 x). 2: { apply BoundIn.pattern_iff. exact Bp. }
        apply Map.in_overriding_union. right. apply Map.in_overriding_union. right. apply U2. exact U.
    + destruct Y as [[NH1 [NS1 [NP1 NL1]]] C1]. destruct Y2 as [[NH2 [NS2 [NP2 NL2]]] C2]. split; intros.
      * invert B.
        -- apply (Y1 x). { apply Map.in_overriding_union. left. exact I. } apply BoundIn.pattern_iff. exact bound_in_pattern.
        -- apply (C2 x). { assumption. } apply Map.in_overriding_union. right. apply Map.in_overriding_union. left. exact I.
        -- apply (C1 x). { exact bound_in_another_case. } exact I.
      * invert U.
        -- apply no_free_vars_1 in used_in_body. apply Map.in_overriding_union in used_in_body as [I | I]. 2: { exact I. }
           edestruct not_shadowed as []. apply BoundIn.pattern_iff. exact I.
        -- apply no_free_vars_2. exact used_in_another_case.
Qed.

Lemma well_formed_in_spec {t context} (no_free_vars : forall x (U : UsedIn.Term t x), Map.In context x)
  : Reflect.Bool (WellFormedNegIn context t) $ well_formed_in context t.
Proof.
  unfold well_formed_in. destruct (@well_formed_in_acc_spec t context no_free_vars context $ fun _ I => I); constructor.
  - exact Y.
  - apply N. exact (pair Map.empty Map.empty).
Qed.



Inductive WellFormedInAcc (cant_bind context : Map.set) : Term.term -> Prop :=
  | Ctr ctor
      : WellFormedInAcc cant_bind context $ Term.Ctr ctor
  | Var {name} (I : Map.In context name) ownership
      : WellFormedInAcc cant_bind context $ Term.Var name ownership
  | App
      {argument bound_or_used_in_function} (Uf
        : forall x, Map.In bound_or_used_in_function x <-> (Map.In cant_bind x \/ BoundIn.Term argument x \/ UsedIn.Term argument x))
      {function bound_or_used_in_argument} (Ua
        : forall x, Map.In bound_or_used_in_argument x <-> (Map.In cant_bind x \/ BoundIn.Term function x \/ UsedIn.Term function x))
      (WFf : WellFormedInAcc bound_or_used_in_function context function)
      (WFa : WellFormedInAcc bound_or_used_in_argument context argument)
      (Db : forall x (Bf : BoundIn.Term function x) (Ba : BoundIn.Term argument x), False)
      : WellFormedInAcc cant_bind context $ Term.App function argument
  | For
      {variable} (NB : forall (I : Map.In cant_bind variable), False)
      {type} (NBt : forall (B : BoundIn.Term type variable), False)
      {body} (NBb : forall (B : BoundIn.Term body variable), False)
      (NUt : forall (U : UsedIn.Term type variable), False)
      {tmp_type} (Ut
        : forall x, Map.In tmp_type x <-> (Map.In cant_bind x \/ BoundIn.Term body x \/ UsedIn.Term body x))
      {bound_or_used_in_type} (Vt : Map.Add variable tt tmp_type bound_or_used_in_type)
      {tmp_body} (Ub
        : forall x, Map.In tmp_body x <-> (Map.In cant_bind x \/ BoundIn.Term type x \/ UsedIn.Term type x))
      {bound_or_used_in_body} (Vb : Map.Add variable tt tmp_body bound_or_used_in_body)
      {body_context} (Cb : Map.Add variable tt context body_context)
      (WFt : WellFormedInAcc bound_or_used_in_type context type)
      (WFb : WellFormedInAcc bound_or_used_in_body body_context body)
      (Db : forall x (Bt : BoundIn.Term type x) (Bb : BoundIn.Term body x), False)
      : WellFormedInAcc cant_bind context $ Term.For variable type body
  | Cas
      {pattern} (WFp : WellFormed.Pattern pattern) (NB : forall x (Bp : BoundIn.Pattern pattern x) (I : Map.In cant_bind x), False)
      {other_cases} (NBo : forall x (Bp : BoundIn.Pattern pattern x) (B : BoundIn.Term other_cases x), False)
      {body_if_match} (NBb : forall x (Bp : BoundIn.Pattern pattern x) (B : BoundIn.Term body_if_match x), False)
      (NUo : forall x (Bp : BoundIn.Pattern pattern x) (U : UsedIn.Term other_cases x), False)
      {tmp_other_cases : Map.set} (Uo
        : forall x, Map.In tmp_other_cases x <-> (
          Map.In cant_bind x \/ BoundIn.Term body_if_match x \/ UsedIn.Term body_if_match x))
      {bound_or_used_in_other_cases} (Vo
        : forall x, Map.In bound_or_used_in_other_cases x <-> (
          BoundIn.Pattern pattern x \/ Map.In tmp_other_cases x))
      {tmp_body_if_match : Map.set} (Ub
        : forall x, Map.In tmp_body_if_match x <-> (
          Map.In cant_bind x \/ BoundIn.Term other_cases x \/ UsedIn.Term other_cases x))
      {bound_or_used_in_body_if_match} (Vb
        : forall x, Map.In bound_or_used_in_body_if_match x <-> (
          BoundIn.Pattern pattern x \/ Map.In tmp_body_if_match x))
      {body_if_match_context} (Cb
        : forall x, Map.In body_if_match_context x <-> (
        BoundIn.Pattern pattern x \/ Map.In context x))
      (WFo : WellFormedInAcc bound_or_used_in_other_cases context other_cases)
      (WFb : WellFormedInAcc bound_or_used_in_body_if_match body_if_match_context body_if_match)
      (Db : forall x (Bo : BoundIn.Term other_cases x) (Bb : BoundIn.Term body_if_match x), False)
      : WellFormedInAcc cant_bind context $ Term.Cas pattern body_if_match other_cases
  .

Definition WellFormedIn context := WellFormedInAcc context context.
Arguments WellFormedIn context t/.

Lemma eq_acc {r1 c1 t1} (WF : WellFormedInAcc r1 c1 t1)
  {r2} (Er : Map.Eq r1 r2) {c2} (Ec : Map.Eq c1 c2) {t2} (Et : t1 = t2)
  : WellFormedInAcc r2 c2 t2.
Proof.
  subst. rename t2 into t. generalize dependent c2. generalize dependent r2. induction WF; intros.
  - constructor.
  - constructor. eapply Map.in_eq. 2: { exact I. } apply Map.eq_sym. exact Ec.
  - econstructor; try exact Db; try apply IHWF1; try apply IHWF2; try apply Map.eq_refl; try exact Ec.
    + intro x. rewrite Uf. split; (intros [I | [B | U]]; [left | right; left; exact B | right; right; exact U]);
      (eapply Map.in_eq; [| exact I]). 2: { exact Er. } apply Map.eq_sym. exact Er.
    + intro x. rewrite Ua. split; (intros [I | [B | U]]; [left | right; left; exact B | right; right; exact U]);
      (eapply Map.in_eq; [| exact I]). 2: { exact Er. } apply Map.eq_sym. exact Er.
  - econstructor.
    + intro I. apply NB. eapply Map.in_eq. 2: { exact I. } apply Er.
    + exact NBt.
    + exact NBb.
    + exact NUt.
    + intro x. rewrite Ut. erewrite (Map.in_eq Er). reflexivity.
    + exact Vt.
    + intro x. rewrite Ub. rewrite <- (Map.in_eq Er). reflexivity.
    + exact Vb.
    + eapply Map.add_eq. { exact Cb. } { reflexivity. } { reflexivity. } { exact Ec. } apply Map.eq_refl.
    + apply IHWF1. { apply Map.eq_refl. } exact Ec.
    + apply IHWF2. { apply Map.eq_refl. } apply Map.eq_refl.
    + intros. apply (Db x). { exact Bt. } exact Bb.
  - econstructor.
    + exact WFp.
    + intros x B I. apply (NB x). { exact B. } eapply Map.in_eq. 2: { exact I. } apply Er.
    + exact NBo.
    + exact NBb.
    + exact NUo.
    + intro x. rewrite Uo. erewrite (Map.in_eq Er). reflexivity.
    + exact Vo.
    + intro x. rewrite Ub. erewrite (Map.in_eq Er). reflexivity.
    + exact Vb.
    + intro x. rewrite Cb. rewrite (Map.in_eq Ec). reflexivity.
    + apply IHWF1. { apply Map.eq_refl. } exact Ec.
    + apply IHWF2. { apply Map.eq_refl. } apply Map.eq_refl.
    + intros. apply (Db x). { exact Bo. } exact Bb.
Qed.

Lemma eq {c1 t1} (WF : WellFormedIn c1 t1)
  {c2} (Ec : Map.Eq c1 c2) {t2} (Et : t1 = t2)
  : WellFormedIn c2 t2.
Proof. eapply eq_acc. { exact WF. } { exact Ec. } { exact Ec. } exact Et. Qed.

Lemma neg_acc cant_bind context t
  : WellFormedInAcc cant_bind context t <-> WellFormedNegInAcc cant_bind context t.
Proof.
  split; intro WF.
  - induction WF; cbn in *.
    + split. { split. { constructor. } repeat split; intro C; invert C. } split; intros. { invert B. } invert U.
    + split. { split. { constructor. } repeat split; intro C; invert C. } split; intros. { invert B. } invert U. exact I.
    + split.
      * split. { constructor. { apply IHWF1. } apply IHWF2. } repeat split; intro C; invert C; try solve [destruct here as [_ [[] _]]];
        try solve [apply IHWF1 in R as []]; try solve [apply IHWF2 in R as []].
        -- destruct here as [x [U B]]. eapply IHWF2. { exact B. } apply Ua. right. right. exact U.
        -- destruct here as [x [U B]]. eapply IHWF1. { exact B. } apply Uf. right. right. exact U.
        -- destruct here as [x [Bf Ba]]. apply (Db x). { exact Bf. } exact Ba.
        -- destruct here as [x [Ba Bf]]. apply (Db x). { exact Bf. } exact Ba.
      * split; intros.
        -- invert B; [eapply IHWF1 | eapply IHWF2]; try eassumption; [apply Uf | apply Ua]; left; exact I.
        -- invert U; [apply IHWF1 | apply IHWF2]; assumption.
    + destruct IHWF1 as [[WPt [Ht [St [Pt Lt]]]] IHt]; destruct IHWF2 as [[WPb [Hb [Sb [Pb Lb]]]] IHb]. split.
      * split. { constructor. { exact WPt. } exact WPb. } repeat split; intro C; invert C.
        -- destruct here as [x [<- B]]. apply NBt in B as [].
        -- destruct here as [x [<- B]]. apply NBb in B as [].
        -- apply Ht in R as [].
        -- apply Hb in R as [].
        -- destruct here as [x [U B]]. eapply IHb in B as [].
           do 2 eapply or_intror in U. apply Ub in U as [[] U]. exists tt. apply Vb. right. exact U.
        -- destruct here as [x [U B]]. eapply IHt in B as []. apply Map.find_tt. apply Vt.
           right. apply Map.find_tt. apply Ut. right. right. exact U.
        -- apply St in R as [].
        -- apply Sb in R as [].
        -- destruct here as [x [Bt Bb]]. apply (Db x). { exact Bt. } exact Bb.
        -- destruct here as [x [Bb Bt]]. apply (Db x). { exact Bt. } exact Bb.
        -- apply Pt in R as [].
        -- apply Pb in R as [].
        -- destruct here as [x [<- U]]. apply NUt in U as [].
        -- destruct lateral as [].
        -- apply Lt in R as [].
        -- apply Lb in R as [].
      * split; intros.
        -- invert B; [apply NB in I as [] | |]. { eapply IHt. { exact bound_in_type. }
             apply Map.find_tt. apply Vt. right. apply Map.find_tt. apply Ut. left. exact I. }
           eapply IHb. { exact bound_in_body. } eapply or_introl in I. apply Ub in I as [[] F]. exists tt. apply Vb. right. exact F.
        -- invert U. { apply IHt. exact used_in_type. } eapply IHb in used_in_body as [[] U].
           apply Cb in U as [[E _] | U]. { apply not_shadowed in E as []. } exists tt. exact U.
    + destruct IHWF1 as [[WPo [Hb [Sb [Pb Lb]]]] IHo]. destruct IHWF2 as [[WPb [Ho [So [Po Lo]]]] IHb]. split.
      * split. { constructor. { exact WFp. } { exact WPb. } exact WPo. }
        repeat split; intro C; invert C.
        -- destruct here as [x [Bp B]]. apply NBb in B as []. exact Bp.
        -- destruct here as [x [Bp B]]. apply NBo in B as []. exact Bp.
        -- apply Ho in R as [].
        -- apply Hb in R as [].
        -- destruct here as [x [U B]]. eapply IHo in B as []. apply Vo. right. apply Uo. right. right. exact U.
        -- destruct here as [x [U B]]. eapply IHb in B as []. apply Vb. right. apply Ub. right. right. exact U.
        -- apply So in R as [].
        -- apply Sb in R as [].
        -- destruct here as [x [Bo Bb]]. apply (Db x). { exact Bb. } exact Bo.
        -- destruct here as [x [Bb Bo]]. apply (Db x). { exact Bb. } exact Bo.
        -- apply Po in R as [].
        -- apply Pb in R as [].
        -- destruct lateral as [].
        -- destruct here as [x [Bp U]]. apply NUo in U as []. exact Bp.
        -- apply Lo in R as [].
        -- apply Lb in R as [].
      * split; intros.
        -- invert B; [apply NB in I as []; exact bound_in_pattern | |].
           ++ eapply IHb. { exact bound_in_body. } apply Vb. right. eapply or_introl in I. apply Ub in I. exact I.
           ++ eapply IHo. { exact bound_in_another_case. } apply Vo. right. apply Uo. left. exact I.
        -- invert U. 2: { apply IHo. exact used_in_another_case. } eapply IHb in used_in_body as I.
           apply Cb in I as [B | I]. { apply not_shadowed in B as []. } exact I.
  - generalize dependent context. generalize dependent cant_bind. induction t; intros; cbn in *.
    + constructor.
    + constructor. apply WF. constructor.
    + destruct WF as [[AP [NH [NS [NP NL]]]] WF]. econstructor.
      * split.
        -- intro I. apply Map.in_overriding_union in I as [I | I]; [left | right]. { exact I. }
           apply Map.in_overriding_union in I as [I | I]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
        -- intro IBU. repeat rewrite Map.in_overriding_union. destruct IBU as [I | [B | U]]; [left; exact I | |]; right;
           [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; assumption.
      * split.
        -- intro I. apply Map.in_overriding_union in I as [I | I]; [left | right]. { exact I. }
           apply Map.in_overriding_union in I as [I | I]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
        -- intro IBU. repeat rewrite Map.in_overriding_union. destruct IBU as [I | [B | U]]; [left; exact I | |]; right;
           [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; assumption.
      * apply IHt1. split. { split. { invert AP. exact APf. }
          repeat split; intro C; [apply NH | apply NS | apply NP | apply NL]; apply ARAF; exact C. }
        split. 2: { intro U. apply WF. apply UsedIn.ApF. exact U. }
        intros. apply Map.in_overriding_union in I as [I | I]. { eapply WF. 2: { exact I. } apply BoundIn.TApF. exact B. }
        apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
        -- apply NP. apply APAF. { constructor. } exists x. split. { exact B. } exact I.
        -- apply NS. apply APAA. { constructor. } exists x. split. { exact I. } exact B.
      * apply IHt2. split. { split. { invert AP. exact APa. }
          repeat split; intro C; [apply NH | apply NS | apply NP | apply NL]; apply ARAA; exact C. }
        split. 2: { intro U. apply WF. apply UsedIn.ApA. exact U. }
        intros. apply Map.in_overriding_union in I as [I | I]. { eapply WF. 2: { exact I. } apply BoundIn.TApA. exact B. }
        apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
        -- apply NP. apply APAA. { constructor. } exists x. split. { exact B. } exact I.
        -- apply NS. apply APAF. { constructor. } exists x. split. { exact I. } exact B.
      * intros. apply NP. apply APAF. { constructor. } exists x. split. { exact Bf. } exact Ba.
    + destruct WF as [[AP [NH [NS [NP NL]]]] WF]. econstructor.
      * apply WF. apply BoundIn.TFoV.
      * intro B. apply NH. apply APFT. exists variable. split. { reflexivity. } exact B.
      * intro B. apply NH. apply APFB. { constructor. } exists variable. split. { reflexivity. } exact B.
      * intro U. apply NL. apply APFT. exists variable. split. { reflexivity. } exact U.
      * split.
        -- intro I. apply Map.in_overriding_union in I as [I | I]; [left | right]. { exact I. }
           apply Map.in_overriding_union in I as [I | I]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
        -- intro IBU. repeat rewrite Map.in_overriding_union. destruct IBU as [I | [B | U]]; [left; exact I | |]; right;
           [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; assumption.
      * apply Map.add_set.
      * split.
        -- intro I. apply Map.in_overriding_union in I as [I | I]; [left | right]. { exact I. }
           apply Map.in_overriding_union in I as [I | I]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
        -- intro IBU. repeat rewrite Map.in_overriding_union. destruct IBU as [I | [B | U]]; [left; exact I | |]; right;
           [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; assumption.
      * apply Map.add_set.
      * apply Map.add_set.
      * apply IHt1. split. { split. { invert AP. exact APt. }
          repeat split; intro C; [apply NH | apply NS | apply NP | apply NL]; apply ARFT; exact C. }
        split. 2: { intro U. apply WF. apply UsedIn.FoT. exact U. } intros. apply Map.in_overriding_add in I as [-> | I]. {
          apply NH. apply APFT. exists variable. split. { reflexivity. } exact B. }
        apply Map.in_overriding_union in I as [I | I]. { eapply WF. 2: { exact I. } apply BoundIn.TFoT. exact B. }
        apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
        -- apply NP. apply APFT. exists x. split. { exact B. } exact I.
        -- apply NS. apply APFB. { constructor. } exists x. split. { exact I. } exact B.
      * apply IHt2. split. { split. { invert AP. exact APb. }
          repeat split; intro C; [apply NH | apply NS | apply NP | apply NL]; apply ARFB; exact C. }
        split. 2: { intro U. apply Map.in_overriding_add. destruct (String.eqb_spec x variable); [left | right]. { exact e. }
          apply WF. apply UsedIn.FoB. 2: { exact U. } exact n. }
        intros. apply Map.in_overriding_add in I as [-> | I]. {
          apply NH. apply APFB. { constructor. } exists variable. split. { reflexivity. } exact B. }
        apply Map.in_overriding_union in I as [I | I]. { apply (WF x). 2: { exact I. } apply BoundIn.TFoB. exact B. }
        apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
        -- apply NP. apply APFT. exists x. split. { exact I. } exact B.
        -- apply NS. apply APFT. exists x. split. { exact I. } exact B.
      * intros. apply NP. apply APFT. exists x. split. { exact Bt. } exact Bb.
    + destruct WF as [[AP [NH [NS [NP NL]]]] WF]. econstructor.
      * invert AP. exact WFp.
      * intros x B. apply WF. apply BoundIn.TCaP. exact B.
      * intros x Bp B. apply NH. apply APCO. exists x. split. { exact Bp. } exact B.
      * intros x Bp B. apply NH. apply APCB. { constructor. } exists x. split. { exact Bp. } exact B.
      * intros x Bp U. apply NL. apply APCO. exists x. split. { exact Bp. } exact U.
      * split.
        -- intro I. apply Map.in_overriding_union in I as [I | I]; [left | right]. { exact I. }
           apply Map.in_overriding_union in I as [I | I]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
        -- intro IBU. repeat rewrite Map.in_overriding_union. destruct IBU as [I | [B | U]]; [left; exact I | |]; right;
           [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; assumption.
      * intro x. rewrite Map.in_overriding_union at 1. rewrite <- (BoundIn.pattern_iff _ _). reflexivity.
      * intro x. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
        rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
      * intro x. rewrite <- (BoundIn.pattern_iff _ _). apply Map.in_overriding_union.
      * intro x. rewrite <- (BoundIn.pattern_iff _ _). apply Map.in_overriding_union.
      * apply IHt2. split. { split. { invert AP. exact APo. }
          repeat split; intro C; [apply NH | apply NS | apply NP | apply NL]; apply ARCO; exact C. }
        split. 2: { intro U. apply WF. apply UsedIn.CaO. exact U. }
        intros. apply Map.in_overriding_union in I as [I | I]. {
          apply NH. apply APCO. exists x. split. { apply BoundIn.pattern_iff. exact I. } exact B. }
        apply Map.in_overriding_union in I as [I | I]. { apply (WF x). { apply BoundIn.TCaO. exact B. } exact I. }
        apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
        -- apply NP. apply APCB. { constructor. } exists x. split. { exact I. } exact B.
        -- apply NS. apply APCB. { constructor. } exists x. split. { exact I. } exact B.
      * apply IHt1. split. { split. { invert AP. exact APb. }
          repeat split; intro C; [apply NH | apply NS | apply NP | apply NL]; apply ARCB; exact C. }
        split; intros. 2: { apply Map.in_overriding_union.
          destruct (BoundIn.pattern_spec pattern x); [left | right]. { apply BoundIn.pattern_iff. exact Y. }
          apply WF. apply UsedIn.CaB. { exact N. } exact U. }
        apply Map.in_overriding_union in I as [I | I]. {
          apply BoundIn.pattern_iff in I. apply NH. apply APCB. { constructor. } exists x. split. { exact I. } exact B. }
        apply Map.in_overriding_union in I as [I | I]. { apply (WF x). 2: { exact I. } apply BoundIn.TCaB. exact B. }
        apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
        -- apply NP. apply APCB. { constructor. } exists x. split. { exact B. } exact I.
        -- apply NS. apply APCO. exists x. split. { exact I. } exact B.
      * intros. apply NP. apply APCO. exists x. split. { exact Bo. } exact Bb.
Qed.

Lemma neg context t
  : WellFormedIn context t <-> WellFormedNegIn context t.
Proof. apply neg_acc. Qed.

Lemma context_superset {cant_bind lil t} (WF : WellFormedInAcc cant_bind lil t)
  {big} (subset : Map.Subset lil big)
  : WellFormedInAcc cant_bind big t.
Proof.
  generalize dependent subset. generalize dependent big. induction WF; intros; cbn in *.
  - constructor.
  - constructor. destruct I as [[] F]. exists tt. apply subset. exact F.
  - econstructor. { exact Uf. } { exact Ua. } { apply IHWF1. exact subset. } { apply IHWF2. exact subset. } exact Db.
  - econstructor. { exact NB. } { exact NBt. } { exact NBb. } { exact NUt. } { exact Ut. } { exact Vt. } { exact Ub. } { exact Vb. }
    { apply Map.add_set. } { apply IHWF1. exact subset. } 2: { exact Db. } apply IHWF2. intros. apply Map.add_set.
    apply Cb in F as [[-> ->] | F]; [left | right]. { split; reflexivity. } apply subset. exact F.
  - econstructor. { exact WFp. } { exact NB. } { exact NBo. } { exact NBb. } { exact NUo. } { exact Uo. } { exact Vo. } { exact Ub. }
    { exact Vb. } { intro x. rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union. } { apply IHWF1. exact subset. }
    2: { exact Db. } apply IHWF2. intros k [] F. apply Map.union_set. eassert (I : Map.In _ _). { exists tt. exact F. }
    apply Cb in I as [I | I]; [left | right]. { apply BoundIn.pattern_iff in I as [[] F']. exact F'. }
    destruct I as [[] F']. apply subset. exact F'.
Qed.

Lemma context_minus {cant_bind big t} (WF : WellFormedInAcc cant_bind big t)
  {x y lil} (A : Map.Add x y lil big)
  (N : Map.In lil x \/ (forall (U : UsedIn.Term t x), False))
  : WellFormedInAcc cant_bind lil t.
Proof.
  destruct y. generalize dependent lil. generalize dependent x. induction WF; intros; cbn in *.
  - constructor.
  - constructor. destruct I as [[] F]. apply A in F as [[-> _] | F]. 2: { exists tt. exact F. }
    destruct N as [I | N]. { exact I. } contradiction N. constructor.
  - econstructor. { exact Uf. } { exact Ua. } 3: { exact Db. }
    + eapply IHWF1. { exact A. } destruct N as [I | N]; [left | right]. { exact I. }
      intro U. apply N. apply UsedIn.ApF. exact U.
    + eapply IHWF2. { exact A. } destruct N as [I | N]; [left | right]. { exact I. }
      intro U. apply N. apply UsedIn.ApA. exact U.
  - econstructor. { exact NB. } { exact NBt. } { exact NBb. } { exact NUt. } { exact Ut. }
    { exact Vt. } { exact Ub. } { exact Vb. } { apply Map.add_set. } 3: { exact Db. }
    + eapply IHWF1. { exact A. } destruct N as [I | N]; [left | right]. { exact I. }
      intro U. apply N. apply UsedIn.FoT. exact U.
    + eapply IHWF2.
      * intros k []. rewrite Cb. rewrite A. rewrite (Map.add_set _).
        rewrite <- or_assoc. rewrite (or_comm (_ /\ _)). rewrite or_assoc. reflexivity.
      * destruct (String.eqb_spec x variable). { left. apply Map.in_overriding_add. left. exact e. }
        destruct N as [I | N]; [left | right]. { apply Map.in_overriding_add. right. exact I. }
        intro U. apply N. apply UsedIn.FoB. { exact n. } exact U.
  - econstructor. { exact WFp. } { exact NB. } { exact NBo. } { exact NBb. } { exact NUo. } { exact Uo. }
    { exact Vo. } { exact Ub. } { exact Vb. } 4: { exact Db. } {
      intros. rewrite <- (BoundIn.pattern_iff _ _). apply Map.in_overriding_union. }
    + eapply IHWF1. { exact A. } destruct N as [I | N]; [left | right]. { exact I. }
      intro U. apply N. apply UsedIn.CaO. exact U.
    + eapply IHWF2.
      * intros k []. rewrite Map.find_tt. rewrite Cb. rewrite <- Map.find_tt. rewrite A. rewrite (Map.union_set _ _ _).
        repeat rewrite Map.find_tt. rewrite (BoundIn.pattern_iff _ _). rewrite <- or_assoc.
        rewrite (or_comm $ BoundIn.Pattern _ _). rewrite or_assoc. reflexivity.
      * destruct (BoundIn.pattern_spec pattern x). { left. apply Map.in_overriding_union. left. apply BoundIn.pattern_iff. exact Y. }
        destruct N as [I | N]; [left | right]. { apply Map.in_overriding_union. right. exact I. }
        intro U. apply N. apply UsedIn.CaB. { exact N0. } exact U.
Qed.

Lemma cant_bind_subset {big context t} (WF : WellFormedInAcc big context t)
  {lil} (subset : Map.Subset lil big)
  : WellFormedInAcc lil context t.
Proof.
  generalize dependent subset. generalize dependent lil. induction WF; intros; cbn in *.
  - constructor.
  - constructor. exact I.
  - econstructor; intros.
    + rewrite <- (BoundIn.term_iff argument x). rewrite <- (UsedIn.term_iff argument x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite <- (BoundIn.term_iff function x). rewrite <- (UsedIn.term_iff function x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + apply IHWF1. intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
      apply Uf. apply Map.union_set in F as [F | F]; [left | right]. { exists tt. eapply subset. exact F. }
      apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.term_iff. exists tt. exact F. }
      apply UsedIn.term_iff. exists tt. exact F.
    + apply IHWF2. intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
      apply Ua. apply Map.union_set in F as [F | F]; [left | right]. { exists tt. eapply subset. exact F. }
      apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.term_iff. exists tt. exact F. }
      apply UsedIn.term_iff. exists tt. exact F.
    + apply (Db x). { exact Bf. } exact Ba.
  - econstructor; intros.
    + destruct I as [[] F]. apply NB. exists tt. apply subset. exact F.
    + apply NBt in B as [].
    + apply NBb in B as [].
    + apply NUt in U as [].
    + rewrite <- (BoundIn.term_iff body x). rewrite <- (UsedIn.term_iff body x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + apply Map.add_set.
    + rewrite <- (BoundIn.term_iff type x). rewrite <- (UsedIn.term_iff type x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + apply Map.add_set.
    + apply Map.add_set.
    + apply IHWF1. intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
      apply Map.find_tt. apply Vt. apply Map.add_set in F as [[-> _] | F]; [left | right]. { split; reflexivity. }
      apply Map.find_tt. apply Ut. apply Map.union_set in F as [F | F]; [left | right]. { exists tt. eapply subset. exact F. }
      apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.term_iff. exists tt. exact F. }
      apply UsedIn.term_iff. exists tt. exact F.
    + eapply context_superset; [apply IHWF2 |]. 2: {
        intros x [] F. apply Map.add_set. apply Cb in F as [[-> _] | F]; [left | right]. { split; reflexivity. } exact F. }
      intros x [] F. apply Vb. apply Map.add_set in F as [[-> _] | F]; [left | right]. { split; reflexivity. }
      apply Map.find_tt. apply Ub. apply Map.union_set in F as [F | F]. { left. exists tt. apply subset. exact F. }
      right. apply Map.union_set in F as [F | F]; [left | right];
      [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; exact F.
    + apply (Db x). { exact Bt. } exact Bb.
  - econstructor; intros.
    + exact WFp.
    + destruct I as [[] F]. apply (NB x). { exact Bp. } exists tt. apply subset. exact F.
    + apply NBo in B as []. exact Bp.
    + apply NBb in B as []. exact Bp.
    + apply NUo in U as []. exact Bp.
    + rewrite <- (BoundIn.term_iff body_if_match x). rewrite <- (UsedIn.term_iff body_if_match x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite Map.in_overriding_union at 1. rewrite <- (BoundIn.pattern_iff _ _). reflexivity.
    + rewrite <- (BoundIn.term_iff other_cases x). rewrite <- (UsedIn.term_iff other_cases x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union.
    + rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union.
    + apply IHWF1. intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
      apply Vo. apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.pattern_iff. exists tt. exact F. }
      apply Uo. apply Map.union_set in F as [F | F]. { left. exists tt. apply subset. exact F. }
      right. apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.term_iff. exists tt. exact F. }
      apply UsedIn.term_iff. exists tt. exact F.
    + eapply context_superset; [apply IHWF2 |]. 2: {
        intros x [] F. apply Map.union_set. eassert (I : Map.In _ _). { exists tt. exact F. }
        apply Cb in I as [I | I]; [left | right]. { apply BoundIn.pattern_iff in I as [[] F']. exact F'. }
        destruct I as [[] F']. exact F'. }
      intros x [] F. apply Map.find_tt. apply Vb. apply Map.union_set in F as [F | F]; [left | right]. {
        apply BoundIn.pattern_iff. exists tt. exact F. }
      apply Ub. apply Map.union_set in F as [F | F]; [left | right]. { exists tt. apply subset. exact F. }
      apply Map.union_set in F as [F | F]; [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; exact F.
    + apply (Db x). { exact Bo. } exact Bb.
Qed.

Lemma cant_bind_union {lil context t} (WF : WellFormedInAcc lil context t)
  {marginal big} (union : Map.Union lil marginal big) (NB : forall x (B : BoundIn.Term t x) (I : Map.In marginal x), False)
  : WellFormedInAcc big context t.
Proof.
  generalize dependent big. generalize dependent marginal. induction WF; intros; cbn in *.
  - constructor.
  - constructor. exact I.
  - econstructor; intros.
    + rewrite <- (BoundIn.term_iff argument x). rewrite <- (UsedIn.term_iff argument x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite <- (BoundIn.term_iff function x). rewrite <- (UsedIn.term_iff function x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + eapply IHWF1. { intros. apply (NB x). { apply BoundIn.TApF. exact B. } exact I. } intros x []. split.
      * intro F. apply Map.union_set in F as [F | F].
        -- apply union in F as [F | F]. 2: { right. exact F. }
           left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Uf. left. exists tt. exact F.
        -- left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Uf. right. apply Map.union_set in F as [F | F]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; assumption.
      * intro FF. apply Map.union_set. rewrite union. destruct FF as [F | F]. 2: { left. right. exact F. }
        eassert (I : Map.In _ _). { exists tt. exact F. } apply Uf in I as [[[] F'] | I]. { left. left. exact F'. }
        right. apply Map.union_set. destruct I as [B | U]; [left | right];
        [apply BoundIn.term_iff in B as [[] F'] | apply UsedIn.term_iff in U as [[] F']]; exact F'.
    + eapply IHWF2. { intros. apply (NB x). { apply BoundIn.TApA. exact B. } exact I. } intros x []. split.
      * intro F. apply Map.union_set in F as [F | F].
        -- apply union in F as [F | F]. 2: { right. exact F. }
           left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Ua. left. exists tt. exact F.
        -- left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Ua. right. apply Map.union_set in F as [F | F]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; assumption.
      * intro FF. apply Map.union_set. rewrite union. destruct FF as [F | F]. 2: { left. right. exact F. }
        eassert (I : Map.In _ _). { exists tt. exact F. } apply Ua in I as [[[] F'] | I]. { left. left. exact F'. }
        right. apply Map.union_set. destruct I as [B | U]; [left | right];
        [apply BoundIn.term_iff in B as [[] F'] | apply UsedIn.term_iff in U as [[] F']]; exact F'.
    + apply (Db x). { exact Bf. } exact Ba.
  - econstructor; intros.
    + destruct I as [[] F]. apply union in F as [F | F]. { apply NB. exists tt. exact F. }
      apply (NB0 variable). { apply BoundIn.TFoV. } exists tt. exact F.
    + apply NBt in B as [].
    + apply NBb in B as [].
    + apply NUt in U as [].
    + rewrite <- (BoundIn.term_iff body x). rewrite <- (UsedIn.term_iff body x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + apply Map.add_set.
    + rewrite <- (BoundIn.term_iff type x). rewrite <- (UsedIn.term_iff type x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + apply Map.add_set.
    + apply Map.add_set.
    + eapply IHWF1. { intros. apply (NB0 x). { apply BoundIn.TFoT. exact B. } exact I. } intros x []. split.
      * intro F. apply Map.add_set in F as [[-> _] | F]. { left. apply Vt. left. split; reflexivity. }
        apply Map.union_set in F as [F | F]. { apply union in F as [F | F]. 2: { right. exact F. }
          left. apply Vt. right. apply Map.find_tt. apply Ut. left. exists tt. exact F. }
        left. apply Vt. right. apply Map.find_tt. apply Ut. right.
        apply Map.union_set in F as [F | F]; [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; exact F.
      * intro FF. apply Map.add_set. repeat rewrite (Map.union_set _ _ _). rewrite union. rewrite or_assoc.
        repeat rewrite Map.find_tt. rewrite (BoundIn.term_iff _ _). rewrite (UsedIn.term_iff _ _).
        destruct FF as [F | F]. 2: { right. right. left. exists tt. exact F. }
        apply Vt in F as [[-> _] | F]; [left | right]. { split; reflexivity. } apply Map.find_tt in F.
        apply Ut in F as [I | [B | U]]. { left. exact I. } { right. right. left. exact B. } right. right. right. exact U.
    + eapply context_superset; [eapply IHWF2 |]. { intros. apply (NB0 x). { apply BoundIn.TFoB. exact B. } exact I. } 2: {
        intros x [] F. apply Map.add_set. apply Cb. exact F. }
      intros x []. rewrite (Map.add_set _). repeat rewrite (Map.union_set _ _ _). rewrite union. rewrite Vb.
      repeat rewrite Map.find_tt. rewrite Ub. repeat rewrite or_assoc. rewrite (BoundIn.term_iff _ _). rewrite (UsedIn.term_iff _ _).
      rewrite (or_comm _ $ Map.In marginal x). repeat rewrite <- (or_assoc _ $ Map.In marginal x).
      rewrite (or_comm (BoundIn.Term type x) $ Map.In marginal x). repeat rewrite or_assoc. reflexivity.
    + apply (Db x). { exact Bt. } exact Bb.
  - econstructor; intros.
    + exact WFp.
    + destruct I as [[] F]. apply union in F as [F | F]. { apply (NB x). { exact Bp. } exists tt. exact F. }
      apply (NB0 x). { apply BoundIn.TCaP. exact Bp. } exists tt. exact F.
    + apply NBo in B as []. exact Bp.
    + apply NBb in B as []. exact Bp.
    + apply NUo in U as []. exact Bp.
    + rewrite (Map.in_overriding_union big). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + rewrite <- (BoundIn.pattern_iff _ _). apply Map.in_overriding_union.
    + rewrite <- (BoundIn.term_iff other_cases x). rewrite <- (UsedIn.term_iff other_cases x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union.
    + rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union.
    + eapply IHWF1. { intros. apply (NB0 x). { apply BoundIn.TCaO. exact B. } exact I. } intros x []. split.
      * intro F. apply Map.union_set in F as [F | F]. {
          left. apply Map.find_tt. apply Vo. left. apply BoundIn.pattern_iff. exists tt. exact F. }
        apply Map.union_set in F as [F | F]. { apply union in F as [F | F]. 2: { right. exact F. }
          left. apply Map.find_tt. apply Vo. right. apply Uo. left. exists tt. exact F. }
        left. apply Map.find_tt. apply Vo. right. apply Uo. right.
        apply Map.union_set in F as [F | F]; [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; exact F.
      * intro FF. repeat rewrite (Map.union_set _ _ _). rewrite union. rewrite or_assoc.
        destruct FF as [F | F]. 2: { right. right. left. exact F. }
        apply Map.find_tt in F as I; clear F. apply Vo in I as [B | I]. { left. apply BoundIn.pattern_iff in B as [[] F]. exact F. }
        right. apply Uo in I as [I | [B | U]]. { left. apply Map.find_tt. exact I. } {
          right. right. left. apply BoundIn.term_iff in B as [[] F]. exact F. } right. right. right.
        apply UsedIn.term_iff in U as [[] F]. exact F.
    + eapply context_superset; [eapply IHWF2 |]. { intros. apply (NB0 x). { apply BoundIn.TCaB. exact B. } exact I. } 2: {
        intros x [] F. apply Map.union_set. destruct (Cb x) as [[B | [[] F']] _]; [exists tt; exact F | left | right]. {
          apply BoundIn.pattern_iff in B as [[] B]. exact B. } exact F'. }
      intros x []. repeat rewrite (Map.union_set _ _ _). rewrite union. repeat rewrite Map.find_tt. rewrite Vb. rewrite Ub.
      repeat rewrite or_assoc. rewrite (BoundIn.term_iff _ _). rewrite (UsedIn.term_iff _ _). rewrite (BoundIn.pattern_iff _ _).
      rewrite (or_comm _ $ Map.In marginal x). rewrite <- (or_assoc (BoundIn.Term other_cases x) $ Map.In marginal x).
      rewrite (or_comm _ $ Map.In marginal x). rewrite or_assoc. reflexivity.
    + apply (Db x). { exact Bo. } exact Bb.
Qed.



Lemma used_before
  {acc cant_bind} (cant_bind_range : forall y (IR : Map.InRange acc y), Map.In cant_bind y)
  {t cant_bind' t'} (E : unshadow_acc acc cant_bind t = Some (cant_bind', t')) {y}
  : UsedIn.Term t' y <-> exists x, (Map.Find acc x y /\ UsedIn.Term t x).
Proof.
  generalize dependent y. generalize dependent t'. generalize dependent cant_bind'.
  generalize dependent cant_bind. generalize dependent acc. induction t; intros.
  - invert E. split. { intro U. invert U. } intros [x [F U]]. invert U.
  - unfold unshadow_acc in E. destruct Map.find eqn:F in E; invert E. apply Map.find_iff in F.
    split. { intro U. invert U. eexists. split. { exact F. } constructor. }
    intros [z [F' U]]. invert U. destruct (Map.find_det F F'). constructor.
  - rewrite unshadow_app in E. destruct unshadow_acc as [[bound_or_used_f f'] |] eqn:Ef in E. 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_a a'] |] eqn:Ea in E; invert E. specialize (IHt1 _ _ cant_bind_range _ _ Ef y).
    eassert (cant_bind_range' : _); [| specialize (IHt2 _ _ cant_bind_range' _ _ Ea y)]. {
      intros z IR. apply (bound_or_used Ef). right. right. apply cant_bind_range. exact IR. }
    split.
    + intro U. invert U.
      * apply IHt1 in used_in_function as [x [F U]]. exists x. split. { exact F. } apply UsedIn.ApF. exact U.
      * apply IHt2 in used_in_argument as [x [F U]]. exists x. split. { exact F. } apply UsedIn.ApA. exact U.
    + intros [x [F U]]. invert U.
      * apply UsedIn.ApF. apply IHt1. exists x. split. { exact F. } exact used_in_function.
      * apply UsedIn.ApA. apply IHt2. exists x. split. { exact F. } exact used_in_argument.
  - rewrite unshadow_for in E. rename t' into term'.
    destruct unshadow_acc as [[bound_or_used_t t'] |] eqn:Et in E. 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in E; invert E.
    eassert (cant_bind_range_t : _); [| specialize (IHt1 _ _ cant_bind_range_t _ _ Et y)]. {
      intros z IR. apply Map.in_overriding_add. right. apply cant_bind_range. exact IR. }
    eassert (cant_bind_range_b : _); [| specialize (IHt2 _ _ cant_bind_range_b _ _ Eb y)]. {
      intros z [x F]. apply (bound_or_used Et). right. right. apply Map.in_overriding_add.
      apply Map.find_overriding_add in F as [[-> ->] | [N F]]; [left | right]. { reflexivity. }
      apply cant_bind_range. exists x. exact F. }
    split.
    + intro U. invert U.
      * apply IHt1 in used_in_type as [x [F U]]. exists x. split. { exact F. } apply UsedIn.FoT. exact U.
      * apply IHt2 in used_in_body as [x [F U]]. apply Map.find_overriding_add in F as [[-> ->] | [N F]]. {
          contradiction not_shadowed. reflexivity. }
        exists x. split. { exact F. } apply UsedIn.FoB. { exact N. } exact U.
    + intros [x [F U]]. invert U.
      * apply UsedIn.FoT. apply IHt1. exists x. split. { exact F. } exact used_in_type.
      * apply UsedIn.FoB. { intros ->. eapply NewNames.not_in_new_name. eapply cant_bind_range. exists x. exact F. }
        apply IHt2. exists x. split. 2: { exact used_in_body. } apply Map.find_overriding_add. right. split; assumption.
  - rewrite unshadow_cas in E. destruct unshadow_acc as [[bound_or_used_o o'] |] eqn:Eo in E. 2: { discriminate E. }
    destruct (Rename.pattern_spec (NewNames.one_to_one_generate cant_bind $ BoundIn.pattern pattern) pattern). 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in E; invert E.
    eassert (cant_bind_range_o : _); [| specialize (IHt2 _ _ cant_bind_range_o _ _ Eo y)]. {
      intros z IR. apply Map.in_overriding_union. right. apply cant_bind_range. exact IR. }
    eassert (cant_bind_range_b : _); [| specialize (IHt1 _ _ cant_bind_range_b _ _ Eb y)]. {
      intros y' [x' F]. apply (bound_or_used Eo). right. right. apply Map.in_overriding_union.
      apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left | right]. { apply Map.in_space_range. exists x'. exact F. }
      apply cant_bind_range. exists x'. exact F. }
    split.
    + intro U. invert U.
      * apply IHt1 in used_in_body as [x' [F U]]. apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. 2: {
          exists x'. split. { exact F. } apply UsedIn.CaB. 2: { exact U. }
          intro B. apply not_shadowed. apply (Rename.bound_in_pattern Y). exists x'. split. { exact B. }
          contradiction N. apply NewNames.in_generate. apply BoundIn.pattern_iff. exact B. }
        contradiction not_shadowed. apply (Rename.bound_in_pattern Y). exists x'. split. 2: { exact F. }
        apply BoundIn.pattern_iff. eapply NewNames.in_generate. exists y. exact F.
      * apply IHt2 in used_in_another_case as [x' [F U]]. exists x'. split. { exact F. } apply UsedIn.CaO. exact U.
    + intros [x' [F U]]. invert U.
      * apply UsedIn.CaB.
        -- intro B. apply (Rename.bound_in_pattern Y) in B as [x'' [B F']].
           eapply NewNames.not_in_generate. 2: { exists x''. exact F'. } apply cant_bind_range. exists x'. exact F.
        -- apply IHt1. exists x'. split. 2: { exact used_in_body. } apply Map.bulk_overwrite_bulk_overwrite. right.
           split. 2: { exact F. } intro I. apply not_shadowed. apply BoundIn.pattern_iff. eapply NewNames.in_generate. exact I.
      * apply UsedIn.CaO. apply IHt2. exists x'. split. { exact F. } exact used_in_another_case.
Qed.

Lemma in_range {acc cant_bind t bound_or_used' t'} (E : unshadow_acc acc cant_bind t = Some (bound_or_used', t'))
  {x} (U : UsedIn.Term t' x)
  : Map.InRange acc x.
Proof.
  generalize dependent x. generalize dependent t'. generalize dependent bound_or_used'.
  generalize dependent cant_bind. generalize dependent acc. induction t; intros.
  - cbn in E. invert E. invert U.
  - cbn in E. destruct (Map.find_spec acc name); invert E. invert U. exists name. exact Y.
  - cbn in E. destruct unshadow_acc as [[bound_or_used_f f'] |] eqn:E1 in E. 2: { discriminate E. }
    specialize (IHt1 _ _ _ _ E1). destruct unshadow_acc as [[bound_or_used_a a'] |] eqn:E2 in E; invert E.
    specialize (IHt2 _ _ _ _ E2). invert U; [apply IHt1 | apply IHt2]; assumption.
  - rewrite unshadow_for in E. destruct unshadow_acc as [[bound_or_used_y y'] |] eqn:E1 in E. 2: { discriminate E. }
    specialize (IHt1 _ _ _ _ E1). destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:E2 in E; invert E.
    specialize (IHt2 _ _ _ _ E2). invert U. { apply IHt1. exact used_in_type. } specialize (IHt2 _ used_in_body) as [z F].
    apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]. { contradiction not_shadowed. reflexivity. }
    exists z. exact F.
  - rewrite unshadow_cas in E. destruct unshadow_acc as [[bound_or_used_o o'] |] eqn:E2 in E. 2: { discriminate E. }
    specialize (IHt2 _ _ _ _ E2). destruct Rename.pattern eqn:ER in E. 2: { discriminate E. }
    apply (Rename.pattern_iff $ NewNames.one_to_one_generate _ _) in ER.
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:E1 in E; invert E.
    specialize (IHt1 _ _ _ _ E1). invert U. 2: { apply IHt2. exact used_in_another_case. }
    specialize (IHt1 _ used_in_body) as [z F]. apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. 2: { exists z. exact F. }
    assert (I : Map.In (BoundIn.pattern pattern) z). { eapply NewNames.in_generate. exists x. exact F. }
    contradiction not_shadowed. apply (Rename.bound_in_pattern ER). exists z.
    split. { apply BoundIn.pattern_iff. eapply NewNames.in_generate. exists x. exact F. } exact F.
Qed.

(* Can't rewrite this in situ below. I'm guessing it has something to do with universes. *)
Lemma what_the_fuck_is_wrong_with_coq_here
  {k T m} (N : Map.find m k = None)
  {v : T} (F : Map.find m k = Some v)
  : False.
Proof. rewrite N in F. discriminate F. Qed.

Lemma or_same P
  : (P \/ P) <-> P.
Proof. split. { intros [p | p]; exact p. } intro p. left. exact p. Qed.

Lemma wf_spec_acc {acc} (O2O : Map.OneToOne acc)
  {cant_bind} (cant_bind_range : forall y (IR : Map.InRange acc y), Map.In cant_bind y)
  {t} (FV : forall x (U : UsedIn.Term t x), Map.In acc x)
  : Reflect.Option (fun '(_, t') =>
      forall ctx (AU : forall x (U : UsedIn.Term t' x), Map.In ctx x),
      WellFormedInAcc cant_bind ctx t'
    ) $ unshadow_acc acc cant_bind t.
Proof.
  generalize dependent cant_bind. generalize dependent acc. induction t; intros.
  - cbn. constructor. constructor.
  - cbn. destruct Map.find eqn:Ef; constructor. { constructor. apply AU. constructor. }
    intros [cant_bind' t'] WF. specialize (FV _ $ UsedIn.Var _ _) as [v F].
    apply Map.find_iff in F. Fail rewrite Ef in F. Fail rewrite F in Ef.
    eapply what_the_fuck_is_wrong_with_coq_here. { exact Ef. } exact F.
  - simpl unshadow_acc.
    eassert (FVf : _); [| specialize (IHt1 acc O2O FVf cant_bind cant_bind_range)]. {
      intros. apply FV. apply UsedIn.ApF. exact U. }
    destruct unshadow_acc as [[bound_or_used_f f'] |] eqn:Ef in IHt1; invert IHt1; rewrite Ef. 2: {
      constructor. contradiction (N (Map.empty, Term.Ctr $ Constructor.Builtin Constructor.Error)). intros. constructor. }
    rename Y into WFf. eassert (FVa : _); [| specialize (IHt2 acc O2O FVa)]. {
      intros. apply FV. apply UsedIn.ApA. exact U. }
    eassert (cant_bind_range_a : _); [| specialize (IHt2 bound_or_used_f cant_bind_range_a)]. {
      intros. apply (bound_or_used Ef). right. right. apply cant_bind_range. exact IR. }
    destruct unshadow_acc as [[bound_or_used_a a'] |] eqn:Ea in IHt2; invert IHt2; rewrite Ea; constructor. 2: {
      contradiction (N (Map.empty, Term.Ctr $ Constructor.Builtin Constructor.Error)). intros. constructor. }
    rename Y into WFa. intros. econstructor.
    + intro x. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + intro x. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + eapply cant_bind_union. { eapply WFf. intros. apply AU. apply UsedIn.ApF. exact U. } { apply Map.union_set. }
      intros. apply Map.in_overriding_union in I as [I | I].
      * apply BoundIn.term_iff in I. eapply (disjoint_bound Ea). 2: { exact I. } apply (bound_or_used Ef). left. exact B.
      * apply UsedIn.term_iff in I. eapply (disjoint_used Ea) in I as [w F]. 2: { apply (bound_or_used Ef). left. exact B. }
        eapply (disjoint_bound Ef). 2: { exact B. } apply cant_bind_range. exists w. exact F.
    + eapply cant_bind_subset. { eapply WFa. intros. apply AU. apply UsedIn.ApA. exact U. }
      intros x [] I. repeat rewrite Map.find_tt in *. apply (bound_or_used Ef).
      apply Map.in_overriding_union in I as [I | I]. { right. right. exact I. }
      apply Map.in_overriding_union in I as [I | I]; [| right]; left; [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
    + intros. eapply (disjoint_bound Ea). 2: { exact Ba. } apply (bound_or_used Ef). left. exact Bf.
  - rewrite unshadow_for. eassert (FVt : _); [| specialize (IHt1 acc O2O FVt)]. { intros. apply FV. apply UsedIn.FoT. exact U. }
    specialize (IHt1 $ Map.set_add (NewNames.new_name cant_bind variable) cant_bind).
    eassert (cant_bind_range_t : _); [| specialize (IHt1 cant_bind_range_t)]. {
      intros y IR. apply Map.in_overriding_add. right. apply cant_bind_range. exact IR. }
    destruct unshadow_acc as [[bound_or_used_t t'] |] eqn:Et in IHt1; invert IHt1; rewrite Et. rename Y into WFt. 2: {
      constructor. contradiction (N (Map.empty, Term.Ctr $ Constructor.Builtin Constructor.Error)). intros. constructor. }
    eassert (O2O' : _); [| specialize (IHt2 (Map.overwrite variable (NewNames.new_name cant_bind variable) acc) O2O')]. {
      unfold Map.OneToOne. intros. apply Map.overwrite_if_present_overwrite in F1 as [[-> ->] | [N1 F1]];
      apply Map.overwrite_if_present_overwrite in F2 as [[-> E2] | [N2 F2]]; subst. { reflexivity. }
      * edestruct (@NewNames.not_in_new_name cant_bind variable) as []. apply cant_bind_range. exists k2. exact F2.
      * edestruct (@NewNames.not_in_new_name cant_bind variable) as []. apply cant_bind_range. exists k1. exact F1.
      * eapply O2O. { exact F1. } exact F2. }
    eassert (FVb : _); [| specialize (IHt2 FVb)]. {
      intros. apply Map.in_overriding_add. destruct (String.eqb_spec x variable); [left | right]. { exact e. }
      apply FV. apply UsedIn.FoB. { exact n. } exact U. }
    eassert (cant_bind_range_b : _); [| specialize (IHt2 bound_or_used_t cant_bind_range_b)]. {
      intros y [x F]. apply (bound_or_used Et). right. right. apply Map.in_overriding_add.
      apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]; [left | right]. { reflexivity. }
      apply cant_bind_range. exists x. exact F. }
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in IHt2; invert IHt2; rewrite Eb; constructor. 2: {
      contradiction (N (Map.empty, Term.Ctr $ Constructor.Builtin Constructor.Error)). intros. constructor. }
    rename Y into WFb. intros. econstructor.
    + apply NewNames.not_in_new_name.
    + intro B. eapply (disjoint_bound Et). 2: { exact B. } apply Map.in_overriding_add. left. reflexivity.
    + intro B. eapply (disjoint_bound Eb). 2: { exact B. }
      apply (bound_or_used Et). right. right. apply Map.in_overriding_add. left. reflexivity.
    + intro U. eapply disjoint_used in U as [k F]. 2: { exact Et. } 2: { apply Map.in_overriding_add. left. reflexivity. }
      eapply NewNames.not_in_new_name. apply cant_bind_range. exists k. exact F.
    + intro x. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + apply Map.add_set.
    + intro x. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + apply Map.add_set.
    + apply Map.add_set.
    + eapply cant_bind_union. { eapply WFt. intros. apply AU. apply UsedIn.FoT. exact U. } {
        intros x []. do 2 erewrite (Map.add_set _) at 1. rewrite or_assoc. erewrite <- (Map.union_set _ _ _). reflexivity. }
      intros. apply Map.in_overriding_union in I as [I | I]. {
        apply BoundIn.term_iff in I. eapply (disjoint_bound Eb). 2: { exact I. } apply (bound_or_used Et). left. exact B. }
      apply UsedIn.term_iff in I. eapply (disjoint_used Eb) in I as [z F]. 2: { apply (bound_or_used Et). left. exact B. }
      eapply (disjoint_bound Et). 2: { exact B. } apply Map.in_overriding_add.
      apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]; [left | right]. { reflexivity. }
      apply cant_bind_range. exists z. exact F.
    + eapply cant_bind_subset. { apply WFb. intros. apply Map.in_overriding_add.
        destruct (String.eqb_spec x $ NewNames.new_name cant_bind variable); [left | right]. { exact e. }
        apply AU. apply UsedIn.FoB. { exact n. } exact U. }
      intros x [] I. repeat rewrite Map.find_tt in *. apply (bound_or_used Et). unfold Map.set_add. rewrite Map.in_overriding_add.
      apply Map.in_overriding_add in I as [-> | I]. { right. right. left. reflexivity. }
      apply Map.in_overriding_union in I as [I | I]. { right. right. right. exact I. }
      apply Map.in_overriding_union in I as [I | I]; [| right]; left; [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
    + intros. eapply (disjoint_bound Eb). 2: { exact Bb. } apply (bound_or_used Et). left. exact Bt.
  - rewrite unshadow_cas. eassert (FVo : _); [| specialize (IHt2 acc O2O FVo)]. { intros. apply FV. apply UsedIn.CaO. exact U. }
    specialize (IHt2 $ Map.set_union (Map.range $ NewNames.generate cant_bind $ BoundIn.pattern pattern) cant_bind).
    eassert (cant_bind_range_o : _); [| specialize (IHt2 cant_bind_range_o)]. {
      intros y IR. apply Map.in_overriding_union. right. apply cant_bind_range. exact IR. }
    destruct unshadow_acc as [[bound_or_used_o o'] |] eqn:Eo in IHt2; invert IHt2; rewrite Eo. rename Y into WFo. 2: {
      constructor. contradiction (N (Map.empty, Term.Ctr $ Constructor.Builtin Constructor.Error)). intros. constructor. }
    destruct (Rename.pattern_spec (NewNames.one_to_one_generate cant_bind $ BoundIn.pattern pattern) pattern). 2: {
      constructor. intros [bound_or_used' t'] WF. Abort.
(* TODO: some measure of equivalence up to renaming, but that's kind of tautological here, since we're *defining* renaming.
 * the problem above is that we're not constraining the result to something *like* the original `t`, so
 * when the reflectee is `None`, we have to prove that no term *at all* *ever* satisfies this pretty easily satisfiable Prop.
 * so, if we want to be extra sure, we should constrain the reflected property s.t. `t` and `t'` are equivalent *)

Lemma on_the_tin_acc
  {acc cant_bind t bound_or_used' t'} (E : unshadow_acc acc cant_bind t = Some (bound_or_used', t'))
  (cant_bind_range : forall y (IR : Map.InRange acc y), Map.In cant_bind y)
  {ctx} (AU : forall x (U : UsedIn.Term t' x), Map.In ctx x)
  : WellFormedInAcc cant_bind ctx t'.
Proof.
  generalize dependent ctx. generalize dependent t'. generalize dependent bound_or_used'.
  generalize dependent cant_bind. generalize dependent acc. { induction t; intros.
  - invert E. constructor.
  - cbn in E. destruct (Map.find_spec acc name); invert E. constructor. apply AU. constructor.
  - cbn in E. destruct unshadow_acc as [[bound_or_used_f f'] |] eqn:Ef in E at 1. 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_a a'] |] eqn:Ea in E at 1; invert E. econstructor.
    + intro. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + intro. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + eapply cant_bind_union. { eapply (IHt1 _ _ _ _ _ Ef). intros. apply AU. apply UsedIn.ApF. exact U. } { apply Map.union_set. }
      intros. apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
      * eapply (disjoint_bound Ea). 2: { exact I. } apply (bound_or_used Ef). left. exact B.
      * eapply (disjoint_used Ea) in I as [z F]. 2: { apply (bound_or_used Ef). left. exact B. }
        eapply (disjoint_bound Ef). 2: { exact B. } apply cant_bind_range. exists z. exact F.
    + eapply cant_bind_subset. { eapply (IHt2 _ _ _ _ _ Ea). intros. apply AU. apply UsedIn.ApA. exact U. }
      intros x [] F. apply Map.find_tt. apply (bound_or_used Ef).
      apply Map.union_set in F as [F | F]. { right. right. exists tt. exact F. }
      apply Map.union_set in F as [F | F]; [| right]; left; [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; exact F.
    + intros. eapply (disjoint_bound Ea). 2: { exact Ba. } apply (bound_or_used Ef). left. exact Bf.
  - rewrite unshadow_for in E. rename t' into term'.
    destruct unshadow_acc as [[bound_or_used_t t'] |] eqn:Et in E at 1. 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in E at 1; invert E. econstructor.
    + apply NewNames.not_in_new_name.
    + intro B. eapply (disjoint_bound Et). 2: { exact B. } apply Map.in_overriding_add. left. reflexivity.
    + intro B. eapply (disjoint_bound Eb). 2: { exact B. }
      apply (bound_or_used Et). right. right. apply Map.in_overriding_add. left. reflexivity.
    + intro U. eapply (disjoint_used Et) in U as [x F]. 2: { apply Map.in_overriding_add. left. reflexivity. }
      eapply NewNames.not_in_new_name. apply cant_bind_range. exists x. exact F.
    + intro. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + apply Map.add_set.
    + intro. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + apply Map.add_set.
    + apply Map.add_set.
    + eapply cant_bind_union. { eapply (IHt1 _ _ _ _ _ Et). intros. apply AU. apply UsedIn.FoT. exact U. } {
        intros x []. fold (Map.set_add $ NewNames.new_name cant_bind variable). repeat rewrite (Map.add_set _) at 1.
        rewrite or_assoc. rewrite <- (Map.union_set _ _ _). reflexivity. }
      intros. apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
      * eapply (disjoint_bound Eb). 2: { exact I. } apply (bound_or_used Et). left. exact B.
      * eapply (disjoint_used Eb) in I as [z F]. 2: { apply (bound_or_used Et). left. exact B. }
        apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]. {
          eapply (disjoint_bound Et). 2: { exact B. } apply Map.in_overriding_add. left. reflexivity. }
        eapply (disjoint_bound Et). 2: { exact B. } apply Map.in_overriding_add. right. apply cant_bind_range. exists z. exact F.
    + eapply cant_bind_subset. { eapply (IHt2 _ _ _ _ _ Eb). intros. apply Map.in_overriding_add.
        destruct (String.eqb_spec x $ NewNames.new_name cant_bind variable); [left | right]. { exact e. }
        apply AU. apply UsedIn.FoB. { exact n. } exact U. }
      intros x [] F. apply Map.find_tt. apply (bound_or_used Et). unfold Map.set_add. rewrite Map.in_overriding_add.
      apply Map.add_set in F as [[-> _] | F]. { right. right. left. reflexivity. }
      apply Map.union_set in F as [F | F]. { right. right. right. exists tt. exact F. }
      apply Map.union_set in F as [F | F]; [| right]; left; [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; exact F.
    + intros. eapply (disjoint_bound Eb). 2: { exact Bb. } apply (bound_or_used Et). left. exact Bt.
  - rewrite unshadow_cas in E. destruct unshadow_acc as [[bound_or_used_o o'] |] eqn:Eo in E at 1. 2: { discriminate E. }
    destruct (Rename.pattern_spec (NewNames.one_to_one_generate cant_bind $ BoundIn.pattern pattern) pattern). 2: { discriminate E. }
    rename Y into R. rename x into p. destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in E at 1; invert E. econstructor.
    + invert R; constructor. invert rename_move_or_reference; constructor; eapply Rename.wf_strict; exact rename_strict.
    + intro y; intros. apply (Rename.bound_in_pattern R) in Bp as [x [Bp F]].
      eapply NewNames.not_in_generate. { exact I. } exists x. exact F.
    + intro y; intros. apply (Rename.bound_in_pattern R) in Bp as [x [Bp F]].
      eapply (disjoint_bound Eo). 2: { exact B. } apply Map.in_overriding_union. left. apply Map.in_space_range. exists x. exact F.
    + intro y; intros. apply (Rename.bound_in_pattern R) in Bp as [x [Bp F]].
      eapply (disjoint_bound Eb). 2: { exact B. } apply (bound_or_used Eo). right. right.
      apply Map.in_overriding_union. left. apply Map.in_space_range. exists x. exact F.
    + intro v; intros. apply (Rename.bound_in_pattern R) in Bp as [x [Bp F]].
      eapply (disjoint_used Eo) in U as [k F']. {
        eapply NewNames.not_in_generate. 2: { exists x. exact F. } apply cant_bind_range. exists k. exact F'. }
      apply Map.in_overriding_union. left. apply Map.in_space_range. exists x. exact F.
    + intro. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + intro. erewrite Map.in_overriding_union at 1. rewrite <- (BoundIn.pattern_iff _ _). reflexivity.
    + intro. rewrite (Map.in_overriding_union cant_bind). rewrite Map.in_overriding_union.
      rewrite <- (BoundIn.term_iff _ _). rewrite <- (UsedIn.term_iff _ _). reflexivity.
    + intro. erewrite Map.in_overriding_union at 1. rewrite <- (BoundIn.pattern_iff _ _). reflexivity.
    + intro. erewrite Map.in_overriding_union at 1. rewrite <- (BoundIn.pattern_iff _ _). reflexivity.
    + eapply cant_bind_union. { eapply (IHt2 _ _ _ _ _ Eo). intros. apply AU. apply UsedIn.CaO. exact U. } {
        intros x []. repeat fold Map.set_union. do 4 erewrite (Map.union_set _ _ _) at 1.
        erewrite Map.find_range at 1. rewrite or_assoc. repeat rewrite Map.find_tt at 1. rewrite (BoundIn.pattern_iff _ _) at 1.
        rewrite (Rename.bound_in_pattern R). split.
        * intros [[z [B F]] | I]; [left | right]. { exists z. exact F. } destruct I as [I | I]; [left | right]. { exact I. }
          rewrite Map.in_overriding_union. exact I.
        * intros [[z F] | I]; [left | right]. { exists z. split. 2: { exact F. }
            apply BoundIn.pattern_iff. eapply NewNames.in_generate. exists x. exact F. }
          destruct I as [I | I]; [left | right]. { exact I. } apply Map.in_overriding_union. exact I. }
      intros. apply Map.in_overriding_union in I as [I | I]; [apply BoundIn.term_iff in I | apply UsedIn.term_iff in I].
      * eapply (disjoint_bound Eb). 2: { exact I. } apply (bound_or_used Eo). left. exact B.
      * eapply (disjoint_used Eb) in I as [z F]. 2: { apply (bound_or_used Eo). left. exact B. }
        apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. { eapply (disjoint_bound Eo). 2: { exact B. }
          apply Map.in_overriding_union. left. apply Map.in_space_range. exists z. exact F. }
        eapply (disjoint_bound Eo). 2: { exact B. } apply Map.in_overriding_union. right. apply cant_bind_range. exists z. exact F.
    + eapply cant_bind_subset. { eapply (IHt1 _ _ _ _ _ Eb). intros. apply Map.in_overriding_union.
        destruct (BoundIn.pattern_spec p x); [left | right]. { apply BoundIn.pattern_iff. exact Y. }
        apply AU. apply UsedIn.CaB. { exact N. } exact U. }
      intros x [] F. rewrite Map.find_tt in *. apply (bound_or_used Eo). rewrite Map.in_overriding_union. rewrite Map.in_space_range.
      apply Map.in_overriding_union in F as [I | I]. { apply BoundIn.pattern_iff in I. right. right. left.
        apply (Rename.bound_in_pattern R) in I as [z [B F]]. exists z. exact F. }
      apply Map.in_overriding_union in I as [I | I]. { right. right. right. exact I. }
      apply Map.in_overriding_union in I as [I | I]; [| right]; left; [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
    + intros. eapply (disjoint_bound Eb). 2: { exact Bb. } apply (bound_or_used Eo). left. exact Bo. }
  Unshelve.
  - exact cant_bind_range.
  - intros. apply (bound_or_used Ef). right. right. apply cant_bind_range. exact IR.
  - intros. apply Map.in_overriding_add. right. apply cant_bind_range. exact IR.
  - intros y [x F]. apply (bound_or_used Et). right. right. apply Map.in_overriding_add.
    apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]; [left | right]. { reflexivity. }
    apply cant_bind_range. exists x. exact F.
  - intros. apply Map.in_overriding_union. right. apply cant_bind_range. exact IR.
  - intros y [x F]. apply (bound_or_used Eo). right. right. apply Map.in_overriding_union. rewrite Map.in_space_range.
    apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left | right]. { exists x. exact F. }
    apply cant_bind_range. exists x. exact F.
Qed.

Lemma on_the_tin_bindings
  {cant_bind t bound_or_used' t'} (E : unshadow_reserve_bindings cant_bind t = Some (bound_or_used', t'))
  {ctx : Map.set} (AU : forall x (U : UsedIn.Term t' x), Map.In ctx x)
  : WellFormedInAcc (Map.set_union cant_bind $ UsedIn.term t) ctx t'.
Proof.
  unfold unshadow_reserve_bindings in E. eapply on_the_tin_acc. { exact E. } 2: { exact AU. }
  intros. apply Map.in_overriding_union. right. destruct IR as [x F]. apply Map.to_self_to_self in F as [I ->]. exact I.
Qed.

Lemma on_the_tin_reserve
  {cant_bind t t'} (E : unshadow_reserve cant_bind t = Some t')
  {ctx : Map.set} (AU : forall x (U : UsedIn.Term t' x), Map.In ctx x)
  : WellFormedInAcc (Map.set_union cant_bind $ UsedIn.term t) ctx t'.
Proof.
  unfold unshadow_reserve in E. destruct unshadow_reserve_bindings as [[] |] eqn:E'; invert E.
  eapply on_the_tin_bindings. { exact E'. } exact AU.
Qed.

Lemma on_the_tin
  {t t'} (E : unshadow t = Some t')
  {ctx : Map.set} (AU : forall x (U : UsedIn.Term t' x), Map.In ctx x)
  : WellFormedInAcc (UsedIn.term t) ctx t'.
Proof.
  eapply on_the_tin_reserve in E. 2 :{ exact AU. } eapply cant_bind_subset. { exact E. }
  intros x [] F. apply Map.union_set. right. exact F.
Qed.



Definition UniqueBindings context :=
  forall k v1 (F1 : Map.Find context k v1) x (B1 : BoundIn.Term v1 x) v2 (F2 : Map.Find context k v2) (B2 : BoundIn.Term v2 x),
  v1 = v2.
Arguments UniqueBindings context/.

Definition WellFormedContextAcc context domain : Prop :=
  UniqueBindings context /\
  Map.ForAll (fun _ => WellFormedInAcc domain domain) context.
Arguments WellFormedContextAcc context domain/.

Definition WellFormedContext context : Prop :=
  forall domain (D : Map.Domain context domain), WellFormedContextAcc context domain.
Arguments WellFormedContext context/.

Definition WellFormedInContext context term : Prop :=
  WellFormedContext context /\
  forall domain (D : Map.Domain context domain),
  forall cant_bind (R : Map.Reflect (fun x => Map.In domain x \/ exists v, (Map.InRange context v /\ BoundIn.Term v x)) cant_bind),
  WellFormedInAcc cant_bind domain term.
Arguments WellFormedInContext context term/.



Definition unshadow_context_each k v (acc : option (Map.set * Context.context)) : option (Map.set * Context.context) :=
  match acc with | None => None | Some (cant_bind, so_far) =>
    match unshadow_reserve_bindings cant_bind v with None => None | Some (bindings, v') =>
      Some (Map.set_union bindings cant_bind, Map.overriding_add k v' so_far)
    end
  end.
Arguments unshadow_context_each k v acc/.

Definition unshadow_context_acc :=
  Map.fold unshadow_context_each.
Arguments unshadow_context_acc/ acc context : rename.

Definition unshadow_context_reserve_bindings cant_bind :=
  unshadow_context_acc (Some (cant_bind, Map.empty)).
Arguments unshadow_context_reserve_bindings cant_bind/ context : rename.

Definition unshadow_context_reserve cant_bind context :=
  option_map snd $ unshadow_context_reserve_bindings cant_bind context.
Arguments unshadow_context_reserve cant_bind context/ : rename.

Definition unshadow_context (context : Context.context) :=
  unshadow_context_reserve (Map.domain context) context.
Arguments unshadow_context context/.

Lemma unfold_right {X Y} (f : X -> Y -> Y) init head tail
  : List.fold_right f init (head :: tail) = f head $ List.fold_right f init tail.
Proof. reflexivity. Qed.

Lemma unshadow_context_prev_spec_acc
  {acc} (Ra : Reflect.Option (fun '(cant_bind', ctx) => Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx) acc) ctx
  : Reflect.Option (fun '(cant_bind', ctx') => Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx) $ unshadow_context_acc acc ctx.
Proof.
  unfold unshadow_context_acc. unfold Map.fold. rewrite MapCore.fold_spec. rewrite <- List.fold_left_rev_right.
  eapply (@Reflect.option_eq _ $ fun '(cant_bind', ctx') => forall k v (F
    : SetoidList.InA MapCore.eq_key_elt (k, v) $ List.rev (MapCore.bindings ctx)), _). {
    intros [cant_bind' ctx']. split; intros H k v F; apply (H k v); [apply -> SetoidList.InA_rev in F |];
    apply MapCore.bindings_spec1 in F; [| apply SetoidList.InA_rev in F]; exact F. }
  remember (List.rev (MapCore.bindings ctx)) as b eqn:Eb; clear ctx Eb.
  generalize dependent acc. induction b as [| [k v] tail IH]; intros. {
    cbn. destruct Ra as [[bindings acc] |]; constructor. { intros k v F. invert F. }
    intros [cant_bind' ctx']. specialize (N (cant_bind', Map.empty)) as []. intros k v F. invert F. }
  rewrite unfold_right. simpl fst. simpl snd. unfold unshadow_context_each at 1. specialize (IH acc Ra).
  destruct IH as [[cant_bind' ctx'] Y |]. 2: { constructor. intros [cant_bind' ctx'] C.
    apply (N (cant_bind', ctx')). intros k' v' F'. eapply C. right. exact F'. }
  destruct (wf_patterns_spec_bindings cant_bind' v) as [[cant_bind'' ctx''] Y' |]; constructor. 2: {
    intros [cant_bind'' ctx''] C. eapply (N (cant_bind'', v)). split; eapply C; left; split; reflexivity. }
  intros k' v' F'. invert F'. { destruct H0. cbn in *. subst. apply Y'. } eapply Y. exact H0.
Qed.

Lemma unshadow_context_prev_spec ctx
  : Reflect.Option (fun _ => Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx) $ unshadow_context ctx.
Proof.
  unfold unshadow_context. unfold unshadow_context_reserve. unfold unshadow_context_reserve_bindings.
  eassert (A : _); [| destruct (@unshadow_context_prev_spec_acc (Some (Map.domain ctx, Map.empty))
    A ctx) as [[] |]]; constructor. { intros k v C. invert C. } { exact Y. }
  intros _ C. apply (N (Map.empty, Map.empty)). exact C.
Qed.

Lemma used_in_acc {acc cant_bind} (CB : forall x y (F : Map.Find acc x y), Map.In cant_bind y)
  {t bindings t'} (E : unshadow_acc acc cant_bind t = Some (bindings, t'))
  {x} (U : UsedIn.Term t x) {y} (F : Map.Find acc x y)
  : UsedIn.Term t' y.
Proof.
  generalize dependent y. generalize dependent x. generalize dependent t'. generalize dependent bindings.
  generalize dependent cant_bind. generalize dependent acc. induction t; intros.
  - invert U.
  - invert U. unfold unshadow_acc in E. destruct Map.find eqn:EF in E; invert E.
    apply Map.find_iff in EF. destruct (Map.find_det F EF). constructor.
  - rewrite unshadow_app in E. destruct unshadow_acc as [[bound_or_used_f f'] |] eqn:Ef in E. 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_a a'] |] eqn:Ea in E; invert E.
    specialize (IHt1 _ _ CB _ _ Ef). eassert (CBa : _); [| specialize (IHt2 _ _ CBa _ _ Ea)]. {
      intros k v F'. apply (bound_or_used Ef). right. right. eapply CB. exact F'. }
    invert U.
    + apply UsedIn.ApF. eapply IHt1. { exact used_in_function. } exact F.
    + apply UsedIn.ApA. eapply IHt2. { exact used_in_argument. } exact F.
  - rewrite unshadow_for in E. rename t' into term'.
    destruct unshadow_acc as [[bound_or_used_t t'] |] eqn:Et in E. 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in E; invert E.
    eassert (CBt : _); [| specialize (IHt1 _ _ CBt _ _ Et)]. {
      intros k v F'. apply Map.in_overriding_add. right. eapply CB. exact F'. }
    eassert (CBb : _); [| specialize (IHt2 _ _ CBb _ _ Eb)]. {
      intros k v F'. apply (bound_or_used Et). right. right. apply Map.in_overriding_add.
      apply Map.overwrite_if_present_overwrite in F' as [[-> ->] | [N' F']]; [left | right]. { reflexivity. }
      eapply CB. exact F'. }
    invert U. { apply UsedIn.FoT. eapply IHt1. { exact used_in_type. } exact F. }
    apply UsedIn.FoB. 2: { eapply IHt2. { exact used_in_body. }
      apply Map.overwrite_if_present_overwrite. right. split. { exact not_shadowed. } exact F. }
    intros ->. eapply NewNames.not_in_new_name. eapply CB. exact F.
  - rewrite unshadow_cas in E.
    destruct unshadow_acc as [[bound_or_used_o o'] |] eqn:Eo in E. 2: { discriminate E. }
    destruct (Rename.pattern_spec (NewNames.one_to_one_generate cant_bind $ BoundIn.pattern pattern) pattern). 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in E; invert E.
    eassert (CBo : _); [| specialize (IHt2 _ _ CBo _ _ Eo)]. {
      intros k v F'. apply Map.in_overriding_union. right. eapply CB. exact F'. }
    eassert (CBb : _); [| specialize (IHt1 _ _ CBb _ _ Eb)]. {
      intros k v F'. apply (bound_or_used Eo). right. right. apply Map.in_overriding_union.
      apply Map.bulk_overwrite_bulk_overwrite in F' as [F' | [N' F']]; [left | right]. { apply Map.in_space_range. exists k. exact F'. }
      eapply CB. exact F'. }
    invert U. 2: { apply UsedIn.CaO. eapply IHt2. { exact used_in_another_case. } exact F. }
    apply UsedIn.CaB. 2: { eapply IHt1. { exact used_in_body. }
      apply Map.bulk_overwrite_bulk_overwrite. right. split. 2: { exact F. }
      intro I. apply NewNames.in_generate in I. apply not_shadowed. apply BoundIn.pattern_iff. exact I. }
    intro B. apply (Rename.bound_in_pattern Y) in B as [z [B F']].
    eapply NewNames.not_in_generate. 2: { exists z. exact F'. } eapply CB. exact F.
Qed.

Lemma used_in_bindings {cant_bind t bindings t'}
  (E : unshadow_reserve_bindings cant_bind t = Some (bindings, t'))
  {x} (U : UsedIn.Term t x)
  : UsedIn.Term t' x.
Proof.
  eapply used_in_acc. 2: { exact E. } 2: { exact U. } 2: {
    apply Map.to_self_to_self. split. { apply UsedIn.term_iff. exact U. } reflexivity. }
  intros. apply Map.in_overriding_union. apply Map.to_self_to_self in F as [I ->]. right. exact I.
Qed.

Lemma eq_spec_unit (a b : unit)
  : Reflect.Bool (a = b) true.
Proof. destruct a. destruct b. constructor. reflexivity. Qed.

Lemma used_idem_acc {acc t} (no_free_vars : forall x (U : UsedIn.Term t x), Map.In acc x)
  {cant_bind} (cant_bind_acc : forall x (I : Map.In acc x), Map.In cant_bind x)
  (cant_bind_range : forall y (IR : Map.InRange acc y), Map.In cant_bind y)
  (A : forall x (U : UsedIn.Term t x) y (F : Map.Find acc x y), y = x)
  {bindings t'} (E : unshadow_acc acc cant_bind t = Some (bindings, t')) {x}
  : UsedIn.Term t' x <-> UsedIn.Term t x.
Proof.
  generalize dependent x. generalize dependent t'. generalize dependent bindings.
  generalize dependent cant_bind. generalize dependent acc. induction t; intros.
  - cbn in E. invert E. reflexivity.
  - unfold unshadow_acc in E. destruct Map.find eqn:F in E; invert E.
    apply Map.find_iff in F. apply A in F as ->. { reflexivity. } constructor.
  - rewrite unshadow_app in E. destruct unshadow_acc as [[bound_or_used_f f'] |] eqn:Ef in E. 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_a a'] |] eqn:Ea in E; invert E.
    eassert (no_free_vars_f : _); [| eassert (Af : _); [|
      specialize (IHt1 _ no_free_vars_f Af _ cant_bind_acc cant_bind_range _ _ Ef)]]. {
      intros. apply no_free_vars. apply UsedIn.ApF. exact U. } {
      intros. apply A. 2: { exact F. } apply UsedIn.ApF. exact U. }
    eassert (no_free_vars_a : _); [| eassert (Aa : _); [| eassert (cant_bind_acc' : _); [| eassert (cant_bind_range' : _); [|
      specialize (IHt2 _ no_free_vars_a Aa _ cant_bind_acc' cant_bind_range' _ _ Ea)]]]]. {
      intros. apply no_free_vars. apply UsedIn.ApA. exact U. } {
      intros. apply A. 2: { exact F. } apply UsedIn.ApA. exact U. } {
      intros. apply (bound_or_used Ef). right. right. apply cant_bind_acc. exact I. } {
      intros. apply (bound_or_used Ef). right. right. apply cant_bind_range. exact IR. }
    split; intro U; (invert U; [apply UsedIn.ApF | apply UsedIn.ApA]; [apply IHt1 | apply IHt2]); assumption.
  - rewrite unshadow_for in E. rename t' into term'.
    destruct unshadow_acc as [[bound_or_used_t t'] |] eqn:Et in E. 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in E; invert E.
    eassert (no_free_vars_t : _); [| eassert (At : _); [| eassert (cant_bind_acc_t : _); [| eassert (cant_bind_range_t : _); [|
      specialize (IHt1 _ no_free_vars_t At _ cant_bind_acc_t cant_bind_range_t _ _ Et)]]]]. {
      intros. apply no_free_vars. apply UsedIn.FoT. exact U. } {
      intros. apply A. 2: { exact F. } apply UsedIn.FoT. exact U. } {
      intros. apply Map.in_overriding_add. right. apply cant_bind_acc. exact I. } {
      intros. apply Map.in_overriding_add. right. apply cant_bind_range. exact IR. }
    eassert (no_free_vars_b : forall x (N : x <> variable) (U : UsedIn.Term t2 x), Map.In acc x). {
      intros. eapply no_free_vars. apply UsedIn.FoB. { exact N. } exact U. }
    eassert (cant_bind_range_b : forall y, Map.InRange (Map.overwrite variable (NewNames.new_name cant_bind variable) acc) y ->
      Map.In bound_or_used_t y). { intros y [z F]. apply (bound_or_used Et). right. right. apply Map.in_overriding_add.
      apply Map.find_overriding_add in F as [[-> ->] | [N F]]; [left | right]. { reflexivity. }
      apply cant_bind_range. exists z. exact F. }
    split.
    + intro U. invert U. { apply UsedIn.FoT. apply IHt1. exact used_in_type. }
      apply (used_before cant_bind_range_b Eb) in used_in_body as [z [F U]].
      apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]. { contradiction not_shadowed. reflexivity. }
      apply A in F as ->; (apply UsedIn.FoB; [exact N | exact U]).
    + intro U. invert U. { apply UsedIn.FoT. apply IHt1. exact used_in_type. }
      apply UsedIn.FoB. 2: { apply (used_before cant_bind_range_b Eb). exists x. split. 2: { exact used_in_body. }
        apply Map.find_overriding_add. right. split. { exact not_shadowed. }
        eassert (I : Map.In _ _). 2: { destruct I as [y F]. assert (y = x). 2: { subst. exact F. }
          apply A. 2: { exact F. } apply UsedIn.FoB. { exact not_shadowed. } exact used_in_body. }
        apply no_free_vars_b. { exact not_shadowed. } apply used_in_body. }
      intros ->. eapply NewNames.not_in_new_name. apply cant_bind_acc. apply no_free_vars.
      apply UsedIn.FoB. { exact not_shadowed. } exact used_in_body.
  - rewrite unshadow_cas in E.
    destruct unshadow_acc as [[bound_or_used_o o'] |] eqn:Eo in E. 2: { discriminate E. }
    destruct (Rename.pattern_spec (NewNames.one_to_one_generate cant_bind $ BoundIn.pattern pattern) pattern). 2: { discriminate E. }
    destruct unshadow_acc as [[bound_or_used_b b'] |] eqn:Eb in E; invert E.
    eassert (no_free_vars_o : _); [| eassert (Ao : _); [| eassert (cant_bind_acc_o : _); [| eassert (cant_bind_range_o : _); [|
      specialize (IHt2 _ no_free_vars_o Ao _ cant_bind_acc_o cant_bind_range_o _ _ Eo)]]]]. {
      intros. apply no_free_vars. apply UsedIn.CaO. exact U. } {
      intros. apply A. 2: { exact F. } apply UsedIn.CaO. exact U. } {
      intros. apply Map.in_overriding_union. right. apply cant_bind_acc. exact I. } {
      intros. apply Map.in_overriding_union. right. apply cant_bind_range. exact IR. }
    eassert (no_free_vars_b : forall x (N : ~BoundIn.Pattern pattern x) (U : UsedIn.Term t1 x), Map.In acc x). {
      intros. eapply no_free_vars. apply UsedIn.CaB. { exact N. } exact U. }
    eassert (cant_bind_range_b : forall y (IR : Map.InRange (Map.bulk_overwrite (NewNames.generate cant_bind $ BoundIn.pattern pattern)
      acc) y), Map.In bound_or_used_o y). { intros y [z F]. apply (bound_or_used Eo). right. right. apply Map.in_overriding_union.
      apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left | right]. { apply Map.in_space_range. exists z. exact F. }
      apply cant_bind_range. exists z. exact F. }
    split.
    + intro U. invert U. 2: { apply UsedIn.CaO. apply IHt2. exact used_in_another_case. }
      apply (used_before cant_bind_range_b Eb) in used_in_body as [z [F U]].
      apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. {
        contradiction not_shadowed. apply (Rename.bound_in_pattern Y). exists z. split. 2: { exact F. }
        apply BoundIn.pattern_iff. eapply NewNames.in_generate. exists x. exact F. }
      apply A in F as ->; (apply UsedIn.CaB; [| exact U]); intro B; apply N;
      apply NewNames.in_generate; apply BoundIn.pattern_iff; exact B.
    + intro U. invert U. 2: { apply UsedIn.CaO. apply IHt2. exact used_in_another_case. }
      apply UsedIn.CaB. 2: { apply (used_before cant_bind_range_b Eb). exists x. split. 2: { exact used_in_body. }
        apply Map.bulk_overwrite_bulk_overwrite. right. split. {
          intro I. apply not_shadowed. apply BoundIn.pattern_iff. eapply NewNames.in_generate. exact I. }
        eassert (I : Map.In _ _). 2: { destruct I as [y F]. assert (y = x). 2: { subst. exact F. }
          apply A. 2: { exact F. } apply UsedIn.CaB. { exact not_shadowed. } exact used_in_body. }
        apply no_free_vars_b. { exact not_shadowed. } apply used_in_body. }
      intro B. apply (Rename.bound_in_pattern Y) in B as [x' [B F]]. eapply NewNames.not_in_generate. 2: { exists x'. exact F. }
      apply cant_bind_acc. apply no_free_vars. apply UsedIn.CaB. { exact not_shadowed. } exact used_in_body.
Qed.

Lemma used_idem {cant_bind t bindings t'} (E : unshadow_reserve_bindings cant_bind t = Some (bindings, t')) {x}
  : UsedIn.Term t' x <-> UsedIn.Term t x.
Proof.
  eapply used_idem_acc; try exact E; intros.
  - apply Map.in_to_self. apply UsedIn.term_iff. exact U.
  - apply Map.in_overriding_union. apply Map.in_to_self in I. right. exact I.
  - apply Map.in_overriding_union. destruct IR as [z F]. apply Map.to_self_to_self in F as [I ->]. right. exact I.
  - apply Map.to_self_to_self in F as [I ->]. reflexivity.
Qed.



(*
Definition cant_bind_ctx (ctx : Map.to Term.term) : Map.set := Todo.
Lemma cant_bind_spec ctx
  : Map.Reflect (fun x => exists t, Map.InRange ctx t /\ (BoundIn.Term t x \/ UsedIn.Term t x)) $ cant_bind_ctx ctx.
Proof. Todo.

Lemma no_free_vars {ctx domain} (WF : WellFormedContextAcc ctx domain)
  {t} (IR : Map.InRange ctx t) {x} (U : UsedIn.Term t x)
  : Map.In ctx x.
Proof.
  destruct IR as [k F]. specialize (WF _ (cant_bind_spec _) _ _ F). cbn in WF.
Qed.
*)

Lemma no_free_vars_acc {cant_bind context t} (WF : WellFormedInAcc cant_bind context t)
  {x} (U : UsedIn.Term t x)
  : Map.In context x.
Proof.
  generalize dependent x. induction WF; intros; cbn in *.
  - invert U.
  - invert U. exact I.
  - invert U. { apply IHWF1. exact used_in_function. } apply IHWF2. exact used_in_argument.
  - invert U. { apply IHWF1. exact used_in_type. } specialize (IHWF2 _ used_in_body). apply Map.find_tt in IHWF2.
    apply Cb in IHWF2 as [[-> _] | F]. { contradiction not_shadowed. reflexivity. } apply Map.find_tt. exact F.
  - invert U. 2: { apply IHWF1. exact used_in_another_case. } specialize (IHWF2 _ used_in_body).
    apply Cb in IHWF2 as [B | I]. { apply not_shadowed in B as []. } exact I.
Qed.



Lemma domain_eq_acc {cant_bind acc ctx bound_or_used ctx'}
  (E : unshadow_context_acc (Some (cant_bind, acc)) ctx = Some (bound_or_used, ctx')) {x}
  : Map.In ctx' x <-> (Map.In acc x \/ Map.In ctx x).
Proof.
  unfold unshadow_context_acc in E. unfold Map.fold in E. rewrite MapCore.fold_spec in E.
  assert (Iff : Map.In ctx x <-> exists y, SetoidList.InA MapCore.eq_key_elt (x, y) $ MapCore.bindings ctx). {
    split; intros [y F]; exists y; apply MapCore.bindings_spec1; exact F. } rewrite Iff. clear Iff.
  remember (MapCore.bindings ctx) as b eqn:Eb; clear ctx Eb. generalize dependent x. generalize dependent ctx'.
  generalize dependent bound_or_used. generalize dependent acc. generalize dependent cant_bind.
  induction b as [| [k v] tail IH]; intros. {
    invert E. split. { intro I. left. exact I. } intros [I | [y I]]. { exact I. } invert I. }
  rewrite NewNames.unfold_left in E. simpl fst in E. simpl snd in E. unfold unshadow_context_each in E at -1.
  destruct unshadow_reserve_bindings as [[this_bindings this_unshadowed_term] |] eqn:E' in E. 2: {
    refine match _ : False with end. clear cant_bind acc k v E' x IH.
    induction tail. { discriminate E. } apply IHtail. exact E. }
  specialize (IH _ _ _ _ E x) as ->. rewrite Map.in_overriding_add. split.
  - intros [[-> | I] | [y I]]. { right. exists v. left. split; reflexivity. } { left. exact I. } right. exists y. right. exact I.
  - intros [I | [y I]]. { left. right. exact I. } invert I. { left. left. apply H0. } right. exists y. exact H0.
Qed.



Lemma on_the_tin_context_acc_acc {so_far tail} (disj : Map.Disjoint so_far tail) {full_context}
  (Rfc : Map.Reflect (fun x => Map.In so_far x \/ Map.In tail x) full_context) (WFsf : WellFormedContextAcc so_far full_context)
  (Nfv : forall k v (F : Map.Find so_far k v \/ Map.Find tail k v) x (U : UsedIn.Term v x), Map.In full_context x)
  {cant_bind_so_far} (Rsf : Map.Reflect (fun x => Map.In full_context x \/
    exists k v, (Map.Find so_far k v /\ BoundIn.Term v x)) cant_bind_so_far)
  {final_bound_or_used final_ctx} (E : unshadow_context_acc (Some (cant_bind_so_far, so_far)) tail =
    Some (final_bound_or_used, final_ctx))
  : WellFormedContextAcc final_ctx full_context.
Proof.
  unfold unshadow_context_acc in E. unfold Map.fold in E. rewrite MapCore.fold_spec in E.
  eassert (disj' : forall k (Is : Map.In so_far k) v (It : SetoidList.InA MapCore.eq_key_elt (k, v) $
    MapCore.bindings tail), False). { intros. eapply disj. { exact Is. }
    exists v. apply MapCore.bindings_spec1. exact It. } clear disj. rename disj' into disj.
  eassert (Rfc' : Map.Reflect (fun x => Map.In so_far x \/
    exists y, SetoidList.InA MapCore.eq_key_elt (x, y) $ MapCore.bindings tail) full_context). {
    intro x. rewrite (Rfc _). split; (intros [I | [y F']]; [left | right]; [exact I |]);
    exists y; apply MapCore.bindings_spec1; exact F'. } clear Rfc. rename Rfc' into Rfc.
  eassert (Nfv' : forall k v (F : Map.Find so_far k v \/ SetoidList.InA MapCore.eq_key_elt (k, v) $ MapCore.bindings tail)
    x (U : UsedIn.Term v x), Map.In full_context x). { intros k' v' F' x U. eapply Nfv. 2: { exact U. }
    destruct F' as [F' | F']; [left | right]. { exact F'. }
    apply MapCore.bindings_spec1. exact F'. } clear Nfv. rename Nfv' into Nfv.
  eassert (ND := MapCore.bindings_spec2w tail). remember (MapCore.bindings tail) as b eqn:Eb; clear tail Eb.
  generalize dependent Nfv. generalize dependent Rfc. generalize dependent disj. generalize dependent Rsf.
  generalize dependent WFsf. generalize dependent final_ctx. generalize dependent final_bound_or_used.
  generalize dependent cant_bind_so_far. generalize dependent so_far.
  induction ND as [| [this_name this_term] tail Nd ND IH]; intros. { invert E. eapply WFsf. }
  rewrite NewNames.unfold_left in E. simpl fst in E. simpl snd in E. unfold unshadow_context_each in E at -1.
  destruct unshadow_reserve_bindings as [[this_bindings this_unshadowed_term] |] eqn:E' in E. 2: {
    refine match _ : False with end.
    clear full_context this_name this_term Nd ND IH so_far disj Rfc cant_bind_so_far E' WFsf Nfv Rsf.
    induction tail. { discriminate E. } apply IHtail. exact E. }
  eapply IH. { exact E. }
  - destruct WFsf as [UB WF]. cbn in UB. cbn in WF. split; intro; intros.
    + apply Map.find_overriding_add in F1 as [[-> ->] | [N1 F1]];
      apply Map.find_overriding_add in F2 as [[tmp ->] | [N2 F2]]; subst;
      [| contradiction N2 | contradiction N1 |]; try reflexivity. eapply UB; eassumption.
    + apply Map.find_overriding_add in F as [[-> ->] | [N F]]. 2: { eapply WF. exact F. }
      eapply cant_bind_subset; [eapply (on_the_tin_bindings E') |]. {
        intros. apply (used_idem E') in U. eapply Nfv. 2: { exact U. } right. left. split; reflexivity. }
      intros x [] F. apply Map.union_set. left. apply Map.find_tt. apply Rsf. left. exists tt. exact F.
  - intro x. rewrite Map.in_overriding_union. rewrite (bound_or_used E' _).
    rewrite Map.in_overriding_union. rewrite (UsedIn.term_iff _ _). rewrite (Rsf _). split.
    + intros [[B | [U | [[I | [k [v [F B]]]] | U]]] | [I | [k [v [F B]]]]].
      * right. exists this_name. exists this_unshadowed_term. split. 2: { exact B. }
        apply Map.find_overriding_add. left. split; reflexivity.
      * apply (used_idem E') in U. left. eapply Nfv. 2: { exact U. } right. left. split; reflexivity.
      * left. exact I.
      * right. exists k. exists v. split. 2: { exact B. } apply Map.find_overriding_add. right. split. 2: { exact F. }
        intros ->. eapply disj. { exists v. exact F. } left. split; reflexivity.
      * left. eapply Nfv. 2: { exact U. } right. left. split; reflexivity.
      * left. exact I.
      * right. exists k. exists v. split. 2: { exact B. } apply Map.find_overriding_add. right. split. 2: { exact F. }
        intros ->. eapply disj. { exists v. exact F. } left. split; reflexivity.
    + intros [I | [k [v [F B]]]]. { left. right. right. left. left. exact I. }
      apply Map.find_overriding_add in F as [[-> ->] | [N F]]. { left. left. exact B. }
      right. right. exists k. exists v. split. { exact F. } exact B.
  - intros. apply Map.in_overriding_add in Is as [-> | Is]. 2: { eapply disj. { exact Is. } right. exact It. }
    eapply Nd. apply Map.eq_key_elt. exists v. exact It.
  - intro x. rewrite (Rfc _). rewrite Map.in_overriding_add. split.
    + intros [I | [y I]]. { left. right. exact I. }
      invert I. { destruct H0; cbn in *; subst. left. left. reflexivity. } right. exists y. exact H0.
    + intros [[-> | I] | [y I]]. { right. exists this_term. left. split; reflexivity. } { left. exact I. }
      right. exists y. right. exact I.
  - intros. destruct F as [F | F]. 2: { apply (Nfv k v). 2: { exact U. } right. right. exact F. }
    apply Map.find_overriding_add in F as [[-> ->] | [N F]]. 2: { apply (Nfv k v). 2: { exact U. } left. exact F. }
    apply (used_idem E') in U. eapply Nfv. 2: { exact U. } right. left. split; reflexivity.
Qed.

Lemma on_the_tin_context_acc {so_far tail} (disj : Map.Disjoint so_far tail) {full_context}
  (Rfc : Map.Reflect (fun x => Map.In so_far x \/ Map.In tail x) full_context) (WFsf : WellFormedContextAcc so_far full_context)
  (Nfv : forall k v (F : Map.Find so_far k v \/ Map.Find tail k v) x (U : UsedIn.Term v x), Map.In full_context x)
  {cant_bind_so_far} (Rsf : Map.Reflect (fun x => Map.In full_context x \/
    exists k v, (Map.Find so_far k v /\ BoundIn.Term v x)) cant_bind_so_far)
  {final_bound_or_used final_ctx} (E : unshadow_context_acc (Some (cant_bind_so_far, so_far)) tail =
    Some (final_bound_or_used, final_ctx))
  : WellFormedContext final_ctx.
Proof.
  unfold WellFormedContext. intros. eapply on_the_tin_context_acc_acc; try exact E; try assumption.
  - intro x. rewrite <- (D _). apply (domain_eq_acc E).
  - destruct WFsf as [UB WF]. split; intro; intros. { eapply UB; eassumption. }
    eapply cant_bind_subset; [eapply context_superset; [eapply WF |] |]. { exact F. }
    + intros x [] I. apply Map.find_tt in I. apply Map.find_tt. apply Rfc in I. apply D. apply (domain_eq_acc E). exact I.
    + intros x [] I. apply Map.find_tt in I. apply Map.find_tt. apply Rfc. apply D in I. apply (domain_eq_acc E) in I. exact I.
  - intros. apply D. apply (domain_eq_acc E). apply Rfc. eapply Nfv. { exact F. } exact U.
  - intro x. rewrite (Rsf _). rewrite (Rfc _). rewrite <- (D _). rewrite (domain_eq_acc E). reflexivity.
Qed.

Lemma on_the_tin_context_bindings
  {context} (Nfv : forall k v (F : Map.Find context k v) x (U : UsedIn.Term v x), Map.In context x)
  {domain} (D : Map.Domain context domain) {final_bound_or_used final_ctx} (E
    : unshadow_context_reserve_bindings domain context = Some (final_bound_or_used, final_ctx))
  : WellFormedContext final_ctx.
Proof.
  eapply on_the_tin_context_acc; try exact E.
  - intros ? C. apply Map.empty_empty in C as [].
  - intro x. rewrite (D _). split. { intro I. right. exact I. }
    intros [I | I]. { apply Map.empty_empty in I as []. } exact I.
  - split; cbn; intros. { invert F1. } invert F.
  - intros. destruct F as [F | F]. { invert F. } apply D. eapply Nfv. { exact F. } exact U.
  - intro x. split. { intro I. left. exact I. }
    intros [I | [k [v [F B]]]]. { exact I. } invert F.
Qed.

Lemma on_the_tin_context_reserve
  {context} (Nfv : forall k v (F : Map.Find context k v) x (U : UsedIn.Term v x), Map.In context x)
  {domain} (D : Map.Domain context domain) {final_ctx} (E
    : unshadow_context_reserve domain context = Some final_ctx)
  : WellFormedContext final_ctx.
Proof.
  unfold unshadow_context_reserve in E. destruct unshadow_context_reserve_bindings as [[] |] eqn:E' in E; invert E.
  eapply on_the_tin_context_bindings; try exact E'; assumption.
Qed.

Lemma on_the_tin_context
  {context} (Nfv : forall k v (F : Map.Find context k v) x (U : UsedIn.Term v x), Map.In context x)
  {final_ctx} (E : unshadow_context context = Some final_ctx)
  : WellFormedContext final_ctx.
Proof. eapply on_the_tin_context_reserve; try exact E. { exact Nfv. } apply Map.domain_domain. Qed.
