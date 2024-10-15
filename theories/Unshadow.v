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
      match Map.find acc k with None => None | Some v => Some (cant_bind, Term.Var v ownership) end
  | Term.App f a =>
      match unshadow_acc acc cant_bind f with None => None | Some (cant_bind, f') =>
        match unshadow_acc acc cant_bind a with None => None | Some (cant_bind, a') =>
          Some (cant_bind, Term.App f' a')
        end
      end
  | Term.For variable type body =>
      match unshadow_acc acc cant_bind type with None => None | Some (cant_bind, type') =>
        let variable' := NewNames.new_name cant_bind variable in
        let acc := Map.overwrite variable variable' acc in
        let cant_bind := Map.set_add variable' cant_bind in
        match unshadow_acc acc cant_bind body with None => None | Some (cant_bind, body') =>
          Some (cant_bind, Term.For variable' type' body')
        end
      end
  | Term.Cas pattern body_if_match other_cases =>
      match unshadow_acc acc cant_bind other_cases with None => None | Some (cant_bind, other_cases') =>
        let bindings := BoundIn.pattern pattern in
        let rebindings := NewNames.generate cant_bind bindings in
        match Rename.pattern rebindings pattern with
        | None => None
        | Some pattern' =>
            let acc := Map.bulk_overwrite rebindings acc in
            let cant_bind := Map.set_union (Map.range rebindings) cant_bind in
            match unshadow_acc acc cant_bind body_if_match with None => None | Some (cant_bind, body_if_match') =>
              Some (cant_bind, Term.Cas pattern' body_if_match' other_cases')
            end
        end
      end
  end.

Definition unshadow_reserve_bindings cant_bind t :=
  let generated := NewNames.generate cant_bind $ UsedIn.term t in
  unshadow_acc generated (Map.set_union cant_bind $ Map.range generated) t.
Arguments unshadow_reserve_bindings cant_bind t/.

Definition unshadow_reserve cant_bind t := option_map snd $ unshadow_reserve_bindings cant_bind t.
Arguments unshadow_reserve cant_bind t/.

Definition unshadow := unshadow_reserve Map.empty.
Arguments unshadow/ t.



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
  generalize dependent a2. generalize dependent a1. { induction t; intros; cbn in *.
  - constructor; assumption.
  - unfold unshadow_acc. destruct (Map.find_spec a1 name).
    + apply Ea in Y. apply Map.find_iff in Y. rewrite Y. constructor. exact Er.
    + destruct (Map.find_spec a2 name). { apply Ea in Y. apply N in Y as []. } constructor.
  - destruct (IHt1 _ _ Ea _ _ Er). { constructor. }
    destruct (IHt2 _ _ Ea _ _ Ecant_bind); constructor; eassumption.
  - destruct (IHt1 _ _ Ea _ _ Er). { constructor. } eassert (Ea' : _); [| eassert (Er' : _); [| destruct (IHt2
      (Map.overriding_add variable (NewNames.new_name cant_bind1 variable) a1)
      (Map.overriding_add variable (NewNames.new_name cant_bind2 variable) a2) Ea'
      (Map.overriding_add (NewNames.new_name cant_bind1 variable) tt cant_bind1)
      (Map.overriding_add (NewNames.new_name cant_bind2 variable) tt cant_bind2) Er')]]. 3: { constructor. }
    + split; intro F; apply Map.find_overriding_add; (apply Map.find_overriding_add in F as [[-> ->] | [N F]]; [left | right];
      [split; [reflexivity | apply NewNames.new_name_det] | split; [exact N |]; apply Ea; exact F]); [| apply Map.eq_sym]; exact Ecant_bind.
    + split; intro F; apply Map.find_overriding_add; (apply Map.find_overriding_add in F as [[-> ->] | [N F]]; [left | right];
      [split; [| reflexivity]; apply NewNames.new_name_det | split; [| apply Ecant_bind; exact F];
        intros ->; contradiction N; apply NewNames.new_name_det]); try exact Ecant_bind; apply Map.eq_sym; exact Ecant_bind.
    + erewrite NewNames.new_name_det. { constructor. exact Ecant_bind0. } exact Ecant_bind.
  - destruct (IHt2 _ _ Ea _ _ Er). { constructor. } destruct Rename.pattern eqn:ER. 2: {
      destruct Rename.pattern eqn:ER2 at 1. 2: { constructor. }
      eapply (Rename.pattern_iff (NewNames.one_to_one_generate _ _)) in ER2.
      eapply (@Rename.pattern_eq _ (NewNames.one_to_one_generate _ _)) in ER2; try reflexivity.
      * eapply Rename.pattern_iff in ER2. rewrite ER2 in ER. discriminate ER.
      * erewrite <- NewNames.generate_det. { apply Map.eq_refl. } { exact Ecant_bind. } apply Map.eq_refl. }
    apply (Rename.pattern_iff (NewNames.one_to_one_generate _ _)) in ER.
    eapply (@Rename.pattern_eq _ (NewNames.one_to_one_generate _ _)) in ER; try reflexivity; [
      eapply Rename.pattern_iff in ER; rewrite ER; clear ER |
      erewrite NewNames.generate_det; try apply Map.eq_refl; exact Ecant_bind].
    eassert (Ea' : _); [| eassert (Er' : _); [| destruct (IHt1
      (Map.overriding_union (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name
        (Map.overriding_union cant_bind1 $ Map.fold (fun _ v acc0 => Map.overriding_add v tt acc0) Map.empty acc) k) acc)
        Map.empty (BoundIn.pattern pattern)) a1)
      (Map.overriding_union (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name
        (Map.overriding_union cant_bind2 $ Map.fold (fun _ v acc0 => Map.overriding_add v tt acc0) Map.empty acc) k) acc)
        Map.empty (BoundIn.pattern pattern)) a2) Ea'
      (Map.overriding_union (Map.fold (fun _ v acc => Map.overriding_add v tt acc) Map.empty
        (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name (Map.overriding_union cant_bind1
          (Map.fold (fun _ v acc0 => Map.overriding_add v tt acc0) Map.empty acc)) k) acc)
          Map.empty (BoundIn.pattern pattern))) cant_bind1)
      (Map.overriding_union (Map.fold (fun _ v acc => Map.overriding_add v tt acc) Map.empty
        (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name (Map.overriding_union cant_bind2
          (Map.fold (fun _ v acc0 => Map.overriding_add v tt acc0) Map.empty acc)) k) acc)
          Map.empty (BoundIn.pattern pattern))) cant_bind2) Er')]]. 3: { constructor. }
    + assert (G := @NewNames.generate_det). cbn in G. erewrite G.
      * split; intro F; apply Map.bulk_overwrite_bulk_overwrite;
        (apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left; exact F | right]);
        (split; [intro I; apply N; exact I |]; apply Ea; exact F).
      * exact Ecant_bind.
      * apply Map.eq_refl.
    + assert (G := @NewNames.generate_det). cbn in G. erewrite G.
      * split; intro F; apply Map.bulk_overwrite_bulk_overwrite;
        (apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left; exact F | right]);
        (split; [intro I; apply N; exact I |]; apply Ecant_bind; exact F).
      * exact Ecant_bind.
      * apply Map.eq_refl.
    + constructor. exact Ecant_bind0. }
  Unshelve.
  - apply NewNames.one_to_one_generate.
  - apply NewNames.one_to_one_generate.
Qed.

Lemma det_reserve
  {r1 r2} (Er : Map.Eq r1 r2)
  {t1 t2} (Et : t1 = t2)
  : unshadow_reserve r1 t1 = unshadow_reserve r2 t2.
Proof.
  unfold unshadow_reserve. unfold unshadow_reserve_bindings.
  eassert (E1 : Map.Eq (NewNames.generate r1 $ UsedIn.term t1) (NewNames.generate r2 $ UsedIn.term t2)). {
    erewrite NewNames.generate_det. { apply Map.eq_refl. } { exact Er. } subst. apply Map.eq_refl. }
  eassert (E2 : Map.Eq
    (Map.set_union r1 $ Map.range $ NewNames.generate r1 $ UsedIn.term t1)
    (Map.set_union r2 $ Map.range $ NewNames.generate r2 $ UsedIn.term t2)). {
    split; intro F; apply Map.bulk_overwrite_bulk_overwrite;
    (apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left; apply Er; exact F | right]);
    (split; [intro I; apply N; eapply Map.in_eq; [| exact I]; try exact Er; apply Map.eq_sym; exact Er |]);
    apply Map.find_range; apply Map.find_range in F as [j F]; eexists; apply E1; exact F. }
  destruct (det_acc E1 E2 Et); reflexivity.
Qed.



Lemma bindings {acc cant_bind term bindings renamed}
  (E : unshadow_acc acc cant_bind term = Some (bindings, renamed))
  (prev : forall x y (Fa : Map.Find acc x y), Map.In cant_bind y)
  : Map.Reflect (fun x => BoundIn.Term renamed x \/ Map.In cant_bind x) bindings.
Proof.
  generalize dependent renamed. generalize dependent bindings.
  generalize dependent cant_bind. generalize dependent acc. induction term; intros; simpl unshadow_acc in *.
  - invert E. split. { intro I. right. exact I. }
    intros [B | I]. { invert B. } exact I.
  - destruct (Map.find_spec acc name) as [name' F | N]; invert E.
    split. { intro I. right. exact I. }
    intros [B | I]. { invert B. } exact I.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E. eapply IHterm1 in E1; try eassumption.
    eapply IHterm2 in E2; try eassumption. 2: { intros. apply E1. right. eapply prev. exact Fa. } split.
    + intro I. apply E2 in I as [B | I].
      * left. apply BoundIn.TApA. exact B.
      * apply E1 in I as [B | I]; [left | right].
        { apply BoundIn.TApF. exact B. } exact I.
    + intro UI. apply E2. destruct UI as [B | I].
      * invert B. 2: { left. exact bound_in_argument. }
        right. apply E1. left. exact bound_in_function.
      * right. apply E1. right. exact I.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    apply IHterm1 in E1. 2: { exact prev. } apply IHterm2 in E2. 2: { intros. apply Map.in_overriding_add.
      apply Map.find_overriding_add in Fa as [[-> ->] | [Na Fa]]; [left | right]. { reflexivity. }
      apply E1. right. eapply prev. exact Fa. } split.
    + intro I. apply E2 in I as [B | I]. { left. apply BoundIn.TFoB. exact B. }
      apply Map.in_overriding_add in I as [-> | I]. { left. apply BoundIn.TFoV. }
      apply E1 in I as [B | I]. { left. apply BoundIn.TFoT. exact B. } right. exact I.
    + intro BI. apply E2. rewrite Map.in_overriding_add.
      destruct BI as [B | I]. 2: { right. right. apply E1. right. exact I. }
      invert B. { right. left. reflexivity. } 2: { left. exact bound_in_body. }
      right. right. apply E1. left. exact bound_in_type.
  - destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct (@Rename.pattern_spec (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name
      (Map.overriding_union r2 (Map.fold (fun _ v acc' => Map.overriding_add v tt acc') Map.empty acc))
      k) acc) Map.empty (BoundIn.pattern pattern)) (NewNames.one_to_one_generate _ _) pattern). 2: { discriminate E. }
    destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E; invert E.
    apply IHterm2 in E2. 2: { exact prev. } apply IHterm1 in E1. 2: {
      intros k v Fa. apply Map.in_overriding_union. rewrite Map.in_range.
      apply Map.bulk_overwrite_bulk_overwrite in Fa as [Fa | [Na Fa]]. { left. eexists. exact Fa. }
      right. apply E2. right. eapply prev. exact Fa. } split.
    + intro I. apply E1 in I as [B | I]. { left. apply BoundIn.TCaB. exact B. }
      apply Map.in_overriding_union in I as [I | I].
      * apply Map.in_range in I as [y0 F]. eassert (I : Map.In _ _). { eexists. exact F. }
        apply NewNames.in_generate in I. apply BoundIn.pattern_iff in I as B.
        eapply Rename.bound_in_pattern in Y. left. apply BoundIn.TCaP. apply Y. eexists. split. { exact B. } exact F.
      * apply E2 in I as [B | I]. { left. apply BoundIn.TCaO. exact B. } right. exact I.
    + intro BI. apply E1. rewrite Map.in_overriding_union. rewrite Map.in_range.
      destruct BI as [B | I]. 2: { right. right. apply E2. right. exact I. }
      invert B. 2: { left. exact bound_in_body. } 2: { right. right. apply E2. left. exact bound_in_another_case. }
      eapply Rename.bound_in_pattern in Y. apply Y in bound_in_pattern as [z [B F]]. right. left. eexists. exact F.
Qed.



Lemma wf_patterns_spec_acc acc cant_bind t
  : Reflect.Option (fun '(cant_bind', t') =>
      WellFormed.AllPatternsIn t /\
      WellFormed.AllPatternsIn t' /\
      forall x (U : UsedIn.Term t x), Map.In acc x
    ) $ unshadow_acc acc cant_bind t.
Proof.
  generalize dependent cant_bind. generalize dependent acc. induction t; intros; cbn in *.
  - constructor. split. { constructor. } split. { constructor. } intros. invert U.
  - destruct (Map.find_spec acc name); constructor.
    + split; intros. { constructor. } split. { constructor. } intros. invert U. eexists. exact Y.
    + intros [cant_bind' t'] [WF [WF' C]]. edestruct C. { constructor. } apply N in H as [].
  - destruct (IHt1 acc cant_bind) as [[r1 t1'] [WF1 [WF1' IH1]] |]. 2: {
      constructor. intros [cant_bind' t'] [WF [WF' C]]. invert WF. eapply (N (cant_bind', t')).
      split. { exact APf. } split. { exact WF'. } intros. apply C. apply UsedIn.ApF. exact U. }
    destruct (IHt2 acc r1) as [[r2 t2'] [WF2 [WF2' IH2]] |]; constructor.
    + split. { constructor; assumption. } split. { constructor. { exact WF1'. } exact WF2'. }
      intros. invert U; [apply IH1 | apply IH2]; assumption.
    + intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APa. } split. { exact WF'. } intros. apply C. apply UsedIn.ApA. exact U.
  - destruct (IHt1 acc cant_bind) as [[r1 t1'] [WF1 [WF1' IH1]] |]. 2: {
      constructor. intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APt. } split. { exact WF'. } intros. apply C. apply UsedIn.FoT. exact U. }
    destruct (IHt2 (Map.overriding_add variable (NewNames.new_name r1 variable) acc)
      (Map.overriding_add (NewNames.new_name r1 variable) tt r1)) as [[r2 t2'] [WF2 [WF2' IH2]] |]; constructor.
    + split. { constructor; assumption. } split. { constructor. { exact WF1'. } exact WF2'. }
      intros. invert U. { apply IH1. exact used_in_type. }
      apply IH2 in used_in_body. apply Map.in_overriding_add in used_in_body as [-> | I]. 2: { exact I. }
      contradiction not_shadowed. reflexivity.
    + intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APb. } split. { exact WF'. } intros. apply Map.in_overriding_add.
      destruct (String.eqb_spec x variable); [left | right]. { assumption. } apply C. apply UsedIn.FoB; assumption.
  - destruct (IHt2 acc cant_bind) as [[r2 t2'] [WF2 [WF2' IH2]] |]. 2: {
      constructor. intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APo. } split. { exact WF'. } intros. apply C. apply UsedIn.CaO. exact U. }
    destruct (@Rename.pattern_spec (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name
      (Map.overriding_union r2 (Map.fold (fun _ v acc'' => Map.overriding_add v tt acc'') Map.empty acc'))
      k) acc') Map.empty (BoundIn.pattern pattern)) (NewNames.one_to_one_generate _ _) pattern). 2: {
      constructor. intros [cant_bind' t'] [WF [WF' C]]. invert WF. eassert (RC : Rename.CompatiblePattern _ _). 2: {
        apply Rename.pattern_iff_compatible in RC as [O2O [renamed R]].
        eapply Rename.pattern_eq in R; try reflexivity. { apply N in R as []. } apply Map.eq_refl. }
      invert WFp; constructor. { apply NewNames.one_to_one_generate. } {
        apply NewNames.in_generate. apply Map.in_singleton. reflexivity. }
      invert move_or_reference_well_formed; constructor; (split; [apply NewNames.one_to_one_generate |]);
      (split; [exact strict_well_formed |]); intros k [] F; apply Map.find_domain;
      apply NewNames.in_generate; cbn; exists tt; exact F. }
    eassert (RC : Rename.CompatiblePattern _ _). { apply Rename.pattern_iff_compatible. do 2 eexists. exact Y. }
    destruct (IHt1
      (Map.overriding_union (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name (Map.overriding_union r2
        (Map.fold (fun _ v acc'' => Map.overriding_add v tt acc'') Map.empty acc')) k) acc') Map.empty (BoundIn.pattern pattern)) acc)
      (Map.overriding_union (Map.fold (fun _ v acc' => Map.overriding_add v tt acc') Map.empty (Map.fold
        (fun k _ acc' => Map.overriding_add k (NewNames.new_name (Map.overriding_union r2 (Map.fold
          (fun _ v acc'' => Map.overriding_add v tt acc'') Map.empty acc')) k) acc')
        Map.empty (BoundIn.pattern pattern))) r2)) as [[r1 t1'] [WF1 [WF1' IH1]] |]; constructor.
    + constructor. { constructor; try assumption. invert RC; constructor. invert C; constructor; apply CS. }
      split. { constructor. 2: { exact WF1'. } 2: { exact WF2'. } invert Y; constructor.
        invert rename_move_or_reference; constructor; eapply Rename.wf_strict; exact rename_strict. }
      intros z U. invert U. 2: { apply IH2. exact used_in_another_case. } apply IH1 in used_in_body.
      apply Map.in_overriding_union in used_in_body as [I | I]. 2: { exact I. }
      apply NewNames.in_generate in I. apply BoundIn.pattern_iff in I. apply not_shadowed in I as [].
    + intros [cant_bind' t'] [WF [WF' C]]. invert WF. apply (N (cant_bind', t')).
      split. { exact APb. } split. { exact WF'. } intros.
      apply Map.in_overriding_union. destruct (BoundIn.pattern_spec pattern x0); [left | right].
      * apply NewNames.in_generate. apply BoundIn.pattern_iff. exact Y0.
      * apply C. apply UsedIn.CaB; assumption.
Qed.

Lemma wf_patterns_spec_bindings cant_bind t
  : Reflect.Option (fun '(cant_bind', t') =>
      WellFormed.AllPatternsIn t /\ WellFormed.AllPatternsIn t'
    ) $ unshadow_reserve_bindings cant_bind t.
Proof.
  unfold unshadow_reserve. unfold unshadow_reserve_bindings.
  destruct (wf_patterns_spec_acc (NewNames.generate cant_bind $ UsedIn.term t)
    (Map.set_union cant_bind $ Map.range $ NewNames.generate cant_bind $ UsedIn.term t) t) as [[domain' renamed] |]; cbn; constructor.
  - destruct Y as [WF [WF' AU]]. split. { exact WF. } exact WF'.
  - intros [cant_bind' t'] [WF WF']. apply (N (cant_bind', t')). split. { exact WF. }
    split. { exact WF'. } intros. apply NewNames.in_generate. apply UsedIn.term_iff. exact U.
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
  (prev : forall x y (Fa : Map.Find acc x y), Map.In cant_bind y)
  {y} (I : Map.In cant_bind y) (U : UsedIn.Term renamed y)
  : exists x, Map.Find acc x y.
Proof.
  generalize dependent y. generalize dependent renamed. generalize dependent cant_bind'.
  generalize dependent cant_bind. generalize dependent acc. induction term; intros; cbn in *.
  - invert E. invert U.
  - destruct (Map.find_spec acc name); invert E. invert U. eexists. exact Y.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    invert U. { eapply IHterm1. { exact prev. } { exact E1. } { exact I. } exact used_in_function. }
    eapply IHterm2. 2: { exact E2. } 3: { exact used_in_argument. }
    + intros. eapply bindings. { exact E1. } { exact prev. } right. eapply prev. exact Fa.
    + eapply bindings. { exact E1. } { exact prev. } right. exact I.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    invert U. { eapply IHterm1. { exact prev. } { exact E1. } { exact I. } exact used_in_type. }
    eapply IHterm2 in E2 as [x IH2]. 4: { exact used_in_body. }
    + apply Map.find_overriding_add in IH2 as [[-> ->] | [N F]]. { contradiction not_shadowed. reflexivity. } eexists. exact F.
    + intros. apply Map.in_overriding_add. apply Map.find_overriding_add in Fa as [[-> ->] | [Na Fa]]; [left | right]. { reflexivity. }
      eapply bindings. { exact E1. } { exact prev. } right. eapply prev. exact Fa.
    + apply Map.in_overriding_add. right. eapply bindings. { exact E1. } { exact prev. } right. exact I.
  - destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct (@Rename.pattern_spec (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name
      (Map.overriding_union r2 (Map.fold (fun _ v acc'' => Map.overriding_add v tt acc'') Map.empty acc'))
      k) acc') Map.empty (BoundIn.pattern pattern)) (NewNames.one_to_one_generate _ _) pattern). 2: { discriminate E. }
    destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E; invert E.
    invert U. 2: { eapply IHterm2. { exact prev. } { exact E2. } { exact I. } exact used_in_another_case. }
    eapply IHterm1 in E1 as [z IH1]. 4: { exact used_in_body. }
    + apply Map.bulk_overwrite_bulk_overwrite in IH1 as [F | [N F]]. 2: { eexists. exact F. }
      eassert (I' : Map.In _ _). { eexists. exact F. } apply NewNames.in_generate in I'. apply BoundIn.pattern_iff in I' as B.
      contradiction not_shadowed. eapply Rename.bound_in_pattern. { exact Y. } eexists. split. { exact B. } exact F.
    + intros k v F. apply Map.in_overriding_union.
      apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. { left. apply Map.in_range. eexists. exact F. }
      right. eapply bindings. { exact E2. } { exact prev. } right. eapply prev. exact F.
    + apply Map.in_overriding_union. right. eapply bindings. { exact E2. } { exact prev. } right. exact I.
Qed.

Lemma disjoint_bound {acc cant_bind term cant_bind' renamed}
  (E : unshadow_acc acc cant_bind term = Some (cant_bind', renamed))
  (prev : forall x y (Fa : Map.Find acc x y), Map.In cant_bind y)
  {x} (I : Map.In cant_bind x) (B : BoundIn.Term renamed x)
  : False.
Proof.
  generalize dependent x. generalize dependent renamed. generalize dependent cant_bind'.
  generalize dependent cant_bind. generalize dependent acc. induction term; intros; cbn in *.
  - invert E. invert B.
  - destruct (Map.find_spec acc name); invert E. invert B.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    invert B. { eapply IHterm1. { exact prev. } { exact E1. } { exact I. } exact bound_in_function. }
    eapply IHterm2. 2: { exact E2. } 3: { exact bound_in_argument. }
    + intros. eapply bindings. { exact E1. } { exact prev. } right. eapply prev. exact Fa.
    + eapply bindings. { exact E1. } { exact prev. } right. exact I.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E. invert B.
    + eapply NewNames.not_in_new_name. eapply bindings. { exact E1. } { exact prev. } right. exact I.
    + eapply IHterm1. { exact prev. } { exact E1. } { exact I. } exact bound_in_type.
    + eapply IHterm2 in E2 as []. 3: { exact bound_in_body. }
      * intros. apply Map.in_overriding_add. apply Map.find_overriding_add in Fa as [[-> ->] | [Na Fa]]. { left. reflexivity. }
        right. eapply bindings. { exact E1. } { exact prev. } right. eapply prev. exact Fa.
      * apply Map.in_overriding_add. right. eapply bindings. { exact E1. } { exact prev. } right. exact I.
  - destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct (@Rename.pattern_spec (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name
      (Map.overriding_union r2 (Map.fold (fun _ v acc'' => Map.overriding_add v tt acc'') Map.empty acc'))
      k) acc') Map.empty (BoundIn.pattern pattern)) (NewNames.one_to_one_generate _ _) pattern). 2: { discriminate E. }
    destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E; invert E. invert B.
    + apply (Rename.bound_in_pattern Y) in bound_in_pattern as [z [B F]]. eapply NewNames.not_in_generate. 2: { eexists. exact F. }
      eapply bindings. { exact E2. } { exact prev. } right. exact I.
    + eapply IHterm1 in E1 as []. 3: { exact bound_in_body. }
      * intros k v F. apply Map.in_overriding_union. rewrite Map.in_range.
        apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. { left. eexists. exact F. }
        right. eapply bindings. { exact E2. } { exact prev. } right. eapply prev. exact F.
      * apply Map.in_overriding_union. rewrite Map.in_range. right. eapply bindings. { exact E2. } { exact prev. } right. exact I.
    + eapply IHterm2. { exact prev. } { exact E2. } { exact I. } exact bound_in_another_case.
Qed.

Lemma used_cant_bind {acc cant_bind term cant_bind' renamed}
  (E : unshadow_acc acc cant_bind term = Some (cant_bind', renamed))
  (prev : forall x y (Fa : Map.Find acc x y), Map.In cant_bind y)
  {x} (U : UsedIn.Term renamed x)
  : Map.In cant_bind' x.
Proof.
  generalize dependent x. generalize dependent renamed. generalize dependent cant_bind'.
  generalize dependent cant_bind. generalize dependent acc. induction term; intros; cbn in *.
  - invert E. invert U.
  - destruct (Map.find_spec acc name); invert E. invert U. eapply prev. exact Y.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E.
    eassert (prev' : forall k v (F : Map.Find acc k v), Map.In r1 v). {
      intros k v F. eapply bindings; try eassumption. right. eapply prev. exact F. }
    invert U. 2: { eapply IHterm2. 2: { eassumption. } 2: { eassumption. } exact prev'. }
    eapply IHterm1 in E1; try eassumption. eapply bindings; try eassumption. right. exact E1.
  - destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E. 2: { discriminate E. }
    eassert (prev' : forall k v (F : Map.Find (Map.overriding_add variable (NewNames.new_name r1 variable) acc) k v),
      Map.In (Map.overriding_add (NewNames.new_name r1 variable) tt r1) v). {
      intros k v F. apply Map.in_overriding_add. apply Map.find_overriding_add in F as [[-> ->] | [N F]]. { left. reflexivity. }
      right. eapply bindings. { exact E1. } { exact prev. } right. eapply prev. exact F. }
    destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E; invert E. invert U. 2: {
      eapply IHterm2. 2: { exact E2. } 2: { exact used_in_body. } exact prev'. }
    eapply IHterm1 in E1; try eassumption. eapply bindings; try eassumption.
    right. apply Map.in_overriding_add. right. exact E1.
  - destruct unshadow_acc as [[r2 t2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct (@Rename.pattern_spec (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name
      (Map.overriding_union r2 (Map.fold (fun _ v acc'' => Map.overriding_add v tt acc'') Map.empty acc'))
      k) acc') Map.empty (BoundIn.pattern pattern)) (NewNames.one_to_one_generate _ _) pattern). 2: { discriminate E. }
    eassert (prev' : forall z y,
      Map.Find (Map.overriding_union (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name
        (Map.overriding_union r2 (Map.fold (fun _ v acc1 => Map.overriding_add v tt acc1) Map.empty acc'))
        k) acc') Map.empty (BoundIn.pattern pattern)) acc) z y ->
      exists v : unit,
      Map.Find (Map.overriding_union (Map.fold (fun (_ v0 : String.string) (acc' : Map.to unit) =>
        Map.overriding_add v0 tt acc') Map.empty (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name
        (Map.overriding_union r2 (Map.fold (fun _ v0 acc1 => Map.overriding_add v0 tt acc1) Map.empty acc'))
        k) acc') Map.empty (BoundIn.pattern pattern))) r2) y v). {
      intros k v F. apply Map.in_overriding_union. rewrite Map.in_range.
      apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. { left. eexists. exact F. }
      right. eapply bindings. { exact E2. } { exact prev. } right. eapply prev. exact F. }
    destruct unshadow_acc as [[r1 t1] |] eqn:E1 in E; invert E. invert U. {
      eapply IHterm1. 2: { exact E1. } 2: { exact used_in_body. } exact prev'. }
    eapply IHterm2 in E2; try eassumption. eapply bindings; try eassumption.
    right. apply Map.in_overriding_union. right. exact E2.
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
        let cant_bind_in_body_without_bindings := Map.set_union cant_bind $ Map.set_union bound_in_type used_in_type in
        if Map.in_ cant_bind_in_body_without_bindings variable then None else
        let cant_bind_in_body := Map.set_add variable cant_bind_in_body_without_bindings in
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
        ) (well_formed_in_acc cant_bind_in_body context_in_body body)
      ) (well_formed_in_acc cant_bind context type)
  | Term.Cas pattern body_if_match other_cases =>
      bind (fun bound_in_other_cases used_in_other_cases =>
        let cant_bind_in_body_without_bindings := Map.set_union cant_bind $ Map.set_union bound_in_other_cases used_in_other_cases in
        if WellFormed.pattern pattern then
          let bound_in_pattern := BoundIn.pattern pattern in
          if Map.disjoint cant_bind_in_body_without_bindings bound_in_pattern then
            let cant_bind_in_body_if_match := Map.set_union bound_in_pattern cant_bind_in_body_without_bindings in
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
            ) (well_formed_in_acc cant_bind_in_body_if_match context_in_body_if_match body_if_match)
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
  {cant_bind} (cant_bind_context : forall x (I : Map.In context x), Map.In cant_bind x)
  : Reflect.Option (fun _ => WellFormedNegInAcc cant_bind context t) $
    well_formed_in_acc cant_bind context t.
Proof.
  generalize dependent cant_bind. generalize dependent context. induction t; intros; cbn in *.
  - constructor. split. { split. { constructor. } repeat split; intro C; invert C. } split; intros. { invert B. } invert U.
  - destruct (Map.in_spec context name); constructor.
    + split. { split. { constructor. } repeat split; intro C; invert C. } split; intros. { invert B. } invert U. exact Y.
    + eintros _ [_ [_ C]]. apply N in C as []. constructor.
  - eassert (no_free_vars_1 : _); [| specialize (IHt1 context no_free_vars_1 cant_bind cant_bind_context)]. {
      intros. apply no_free_vars. apply UsedIn.ApF. exact U. }
    destruct well_formed_in_acc as [[b1 u1] |] eqn:E1 in IHt1; rewrite E1; invert IHt1. 2: {
      constructor. intros pair [[AP [NH [NS [NP NL]]]] C]. apply (N pair). split. 2: { intro x. specialize (C x) as [C1 C2].
        split; intros; [apply C1 | apply C2]. { apply BoundIn.TApF. exact B. } { exact I. } apply UsedIn.ApF. exact U. }
      split. { invert AP. exact APf. } repeat split; intro; [apply NH | apply NS | apply NP | apply NL]; apply ARAF; assumption. }
    eassert (no_free_vars_2 : _); [| specialize (IHt2 context no_free_vars_2 cant_bind cant_bind_context)]. {
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
  - eassert (no_free_vars_1 : _); [| specialize (IHt1 context no_free_vars_1 cant_bind cant_bind_context)]. {
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
    eassert (cant_bind_context' : _); [| specialize (IHt2 cant_bind_context')]. {
      intro x. repeat rewrite Map.in_overriding_add. destruct (String.eqb_spec x variable); [left | right]. { exact e. }
      destruct I as [E | I]. { apply n in E as []. } repeat rewrite Map.in_overriding_union. left. apply cant_bind_context. exact I. }
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
  - eassert (no_free_vars_2 : _); [| specialize (IHt2 context no_free_vars_2 cant_bind cant_bind_context)]. {
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
    eassert (cant_bind_context' : _); [| specialize (IHt1 cant_bind_context')]. {
      intro x. repeat rewrite Map.in_overriding_union. intros [I | I]; [left | right]. { exact I. }
      left. apply cant_bind_context. exact I. }
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
      {argument cant_bind_in_function} (Uf
        : forall x, Map.In cant_bind_in_function x <-> (Map.In cant_bind x \/ BoundIn.Term argument x \/ UsedIn.Term argument x))
      {function cant_bind_in_argument} (Ua
        : forall x, Map.In cant_bind_in_argument x <-> (Map.In cant_bind x \/ BoundIn.Term function x \/ UsedIn.Term function x))
      (WFf : WellFormedInAcc cant_bind_in_function context function)
      (WFa : WellFormedInAcc cant_bind_in_argument context argument)
      (Db : forall x (Bf : BoundIn.Term function x) (Ba : BoundIn.Term argument x), False)
      : WellFormedInAcc cant_bind context $ Term.App function argument
  | For
      {variable} (NB : forall (I : Map.In cant_bind variable), False)
      {type} (NBt : forall (B : BoundIn.Term type variable), False)
      {body} (NBb : forall (B : BoundIn.Term body variable), False)
      (NUt : forall (U : UsedIn.Term type variable), False)
      {cant_bind_in_type} (Ut
        : forall x, Map.In cant_bind_in_type x <-> (Map.In cant_bind x \/ BoundIn.Term body x \/ UsedIn.Term body x))
      {tmp_body} (Tb
        : forall x, Map.In tmp_body x <-> (Map.In cant_bind x \/ BoundIn.Term type x \/ UsedIn.Term type x))
      {cant_bind_in_body} (Ub : Map.Add variable tt tmp_body cant_bind_in_body)
      {body_context} (Cb : Map.Add variable tt context body_context)
      (WFt : WellFormedInAcc cant_bind_in_type context type)
      (WFb : WellFormedInAcc cant_bind_in_body body_context body)
      (Db : forall x (Bt : BoundIn.Term type x) (Bb : BoundIn.Term body x), False)
      : WellFormedInAcc cant_bind context $ Term.For variable type body
  | Cas
      {pattern} (WFp : WellFormed.Pattern pattern) (NB : forall x (Bp : BoundIn.Pattern pattern x) (I : Map.In cant_bind x), False)
      {other_cases} (NBo : forall x (Bp : BoundIn.Pattern pattern x) (B : BoundIn.Term other_cases x), False)
      {body_if_match} (NBb : forall x (Bp : BoundIn.Pattern pattern x) (B : BoundIn.Term body_if_match x), False)
      (NUo : forall x (Bp : BoundIn.Pattern pattern x) (U : UsedIn.Term other_cases x), False)
      {cant_bind_in_other_cases} (Uo
        : forall x, Map.In cant_bind_in_other_cases x <-> (
          Map.In cant_bind x \/ BoundIn.Term body_if_match x \/ UsedIn.Term body_if_match x))
      {tmp_body_if_match : Map.set} (Tb
        : forall x, Map.In tmp_body_if_match x <-> (
          Map.In cant_bind x \/ BoundIn.Term other_cases x \/ UsedIn.Term other_cases x))
      {cant_bind_in_body_if_match} (Ub
        : forall x, Map.In cant_bind_in_body_if_match x <-> (
          BoundIn.Pattern pattern x \/ Map.In tmp_body_if_match x))
      {body_if_match_context} (Cb
        : forall x, Map.In body_if_match_context x <-> (
        BoundIn.Pattern pattern x \/ Map.In context x))
      (WFo : WellFormedInAcc cant_bind_in_other_cases context other_cases)
      (WFb : WellFormedInAcc cant_bind_in_body_if_match body_if_match_context body_if_match)
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
    + intro x. rewrite Tb. erewrite (Map.in_eq Er). reflexivity.
    + exact Ub.
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
    + intro x. rewrite Tb. erewrite (Map.in_eq Er). reflexivity.
    + intro x. rewrite Ub. reflexivity.
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
           do 2 eapply or_intror in U. apply Tb in U as [[] U]. exists tt. apply Ub. right. exact U.
        -- destruct here as [x [U B]]. eapply IHt in B as []. apply Ut. right. right. exact U.
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
        -- invert B; [apply NB in I as [] | |]. { eapply IHt. { exact bound_in_type. } apply Ut. left. exact I. }
           eapply IHb. { exact bound_in_body. } eapply or_introl in I. apply Tb in I as [[] F]. exists tt. apply Ub. right. exact F.
        -- invert U. { apply IHt. exact used_in_type. } eapply IHb in used_in_body as [[] U].
           apply Cb in U as [[E _] | U]. { apply not_shadowed in E as []. } exists tt. exact U.
    + destruct IHWF1 as [[WPo [Hb [Sb [Pb Lb]]]] IHo]. destruct IHWF2 as [[WPb [Ho [So [Po Lo]]]] IHb]. split.
      * split. { constructor. { exact WFp. } { exact WPb. } exact WPo. }
        repeat split; intro C; invert C.
        -- destruct here as [x [Bp B]]. apply NBb in B as []. exact Bp.
        -- destruct here as [x [Bp B]]. apply NBo in B as []. exact Bp.
        -- apply Ho in R as [].
        -- apply Hb in R as [].
        -- destruct here as [x [U B]]. eapply IHo in B as []. apply Uo. right. right. exact U.
        -- destruct here as [x [U B]]. eapply IHb in B as []. apply Ub. right. apply Tb. right. right. exact U.
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
           ++ eapply IHb. { exact bound_in_body. } apply Ub. right. eapply or_introl in I. apply Tb in I. exact I.
           ++ eapply IHo. { exact bound_in_another_case. } apply Uo. left. exact I.
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
        split. 2: { intro U. apply WF. apply UsedIn.FoT. exact U. }
        intros. apply Map.in_overriding_union in I as [I | I]. { eapply WF. 2: { exact I. } apply BoundIn.TFoT. exact B. }
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
      * split.
        -- intro I. apply Map.in_overriding_union in I as [I | I]; [left | right]. { exact I. }
           apply Map.in_overriding_union in I as [I | I]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exact I.
        -- intro IBU. repeat rewrite Map.in_overriding_union. destruct IBU as [I | [B | U]]; [left; exact I | |]; right;
           [left | right]; [apply BoundIn.term_iff | apply UsedIn.term_iff]; assumption.
      * intro x. assert (B := BoundIn.pattern_iff). cbn in B. rewrite <- B. apply Map.in_overriding_union.
      * intro x. assert (B := BoundIn.pattern_iff). cbn in B. rewrite <- B. apply Map.in_overriding_union.
      * apply IHt2. split. { split. { invert AP. exact APo. }
          repeat split; intro C; [apply NH | apply NS | apply NP | apply NL]; apply ARCO; exact C. }
        split. 2: { intro U. apply WF. apply UsedIn.CaO. exact U. }
        intros. apply Map.in_overriding_union in I as [I | I]. { apply (WF x). { apply BoundIn.TCaO. exact B. } exact I. }
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
  - econstructor. { exact NB. } { exact NBt. } { exact NBb. } { exact NUt. } { exact Ut. } { exact Tb. } { exact Ub. }
    { apply Map.add_set. } { apply IHWF1. exact subset. } 2: { exact Db. } apply IHWF2. intros. apply Map.add_set.
    apply Cb in F as [[-> ->] | F]; [left | right]. { split; reflexivity. } apply subset. exact F.
  - econstructor. { exact WFp. } { exact NB. } { exact NBo. } { exact NBb. } { exact NUo. } { exact Uo. } { exact Tb. } { exact Ub. }
    { intro x. rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union. } { apply IHWF1. exact subset. }
    2: { exact Db. } apply IHWF2. intros k [] F. apply Map.union_set. eassert (I : Map.In _ _). { exists tt. exact F. }
    apply Cb in I as [I | I]; [left | right]. { apply BoundIn.pattern_iff in I as [[] F']. exact F'. }
    destruct I as [[] F']. apply subset. exact F'.
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
    + rewrite <- (BoundIn.term_iff type x). rewrite <- (UsedIn.term_iff type x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + apply Map.add_set.
    + apply Map.add_set.
    + apply IHWF1. intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
      apply Ut. apply Map.union_set in F as [F | F]; [left | right]. { exists tt. eapply subset. exact F. }
      apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.term_iff. exists tt. exact F. }
      apply UsedIn.term_iff. exists tt. exact F.
    + eapply context_superset; [apply IHWF2 |]. 2: {
        intros x [] F. apply Map.add_set. apply Cb in F as [[-> _] | F]; [left | right]. { split; reflexivity. } exact F. }
      intros x [] F. apply Ub. apply Map.add_set in F as [E | F]; [left | right]. { exact E. }
      eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. } apply Tb.
      apply Map.union_set in F as [F | F]; [left | right]. { exists tt. apply subset. exact F. }
      apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.term_iff. exists tt. exact F. }
      apply UsedIn.term_iff. exists tt. exact F.
    + apply (Db x). { exact Bt. } exact Bb.
  - econstructor; intros.
    + exact WFp.
    + destruct I as [[] F]. apply (NB x). { exact Bp. } exists tt. apply subset. exact F.
    + apply NBo in B as []. exact Bp.
    + apply NBb in B as []. exact Bp.
    + apply NUo in U as []. exact Bp.
    + rewrite <- (BoundIn.term_iff body_if_match x). rewrite <- (UsedIn.term_iff body_if_match x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite <- (BoundIn.term_iff other_cases x). rewrite <- (UsedIn.term_iff other_cases x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union.
    + rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union.
    + apply IHWF1. intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
      apply Uo. apply Map.union_set in F as [F | F]; [left | right]. { exists tt. eapply subset. exact F. }
      apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.term_iff. exists tt. exact F. }
      apply UsedIn.term_iff. exists tt. exact F.
    + eapply context_superset; [apply IHWF2 |]. 2: {
        intros x [] F. apply Map.union_set. eassert (I : Map.In _ _). { exists tt. exact F. }
        apply Cb in I as [I | I]; [left | right]. { apply BoundIn.pattern_iff in I as [[] F']. exact F'. }
        destruct I as [[] F']. exact F'. }
      intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. } apply Ub.
      apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.pattern_iff. exists tt. exact F. }
      apply Tb. apply Map.union_set in F as [F | F]; [left | right]. { exists tt. apply subset. exact F. }
      apply Map.union_set in F as [F | F]; [left | right]. { apply BoundIn.term_iff. exists tt. exact F. }
      apply UsedIn.term_iff. exists tt. exact F.
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
    + rewrite <- (BoundIn.term_iff type x). rewrite <- (UsedIn.term_iff type x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + apply Map.add_set.
    + apply Map.add_set.
    + eapply IHWF1. { intros. apply (NB0 x). { apply BoundIn.TFoT. exact B. } exact I. } intros x []. split.
      * intro F. apply Map.union_set in F as [F | F].
        -- apply union in F as [F | F]. 2: { right. exact F. }
           left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Ut. left. exists tt. exact F.
        -- left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Ut. right. apply Map.union_set in F as [F | F]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; assumption.
      * intro FF. apply Map.union_set. rewrite union. destruct FF as [F | F]. 2: { left. right. exact F. }
        eassert (I : Map.In _ _). { exists tt. exact F. } apply Ut in I as [[[] F'] | I]. { left. left. exact F'. }
        right. apply Map.union_set. destruct I as [B | U]; [left | right];
        [apply BoundIn.term_iff in B as [[] F'] | apply UsedIn.term_iff in U as [[] F']]; exact F'.
    + eapply context_superset; [eapply IHWF2 |]. { intros. apply (NB0 x). { apply BoundIn.TFoB. exact B. } exact I. } 2: {
        intros x [] F. apply Map.add_set. apply Cb. exact F. } intros x []. split.
      * intro F. apply Map.add_set in F as [[-> _] | F]. { left. apply Ub. left. split; reflexivity. }
        apply Map.union_set in F as [F | F].
        -- apply union in F as [F | F]. 2: { right. exact F. }
           left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           exists tt. apply Ub. right. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Tb. left. exists tt. exact F.
        -- left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           exists tt. apply Ub. right. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Tb. right. apply Map.union_set in F as [F | F]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; assumption.
      * intro FF. apply Map.add_set. assert (E := Map.union_set); cbn in E; repeat rewrite E; clear E.
        rewrite union. destruct FF as [F | F]. 2: { right. left. right. exact F. }
        apply Ub in F as [E | F]; [left | right]. { exact E. }
        eassert (I : Map.In _ _). { exists tt. exact F. } apply Tb in I as [[[] F'] | I]. { left. left. exact F'. }
        right. destruct I as [B | U]; [left | right];
        [apply BoundIn.term_iff in B as [[] F'] | apply UsedIn.term_iff in U as [[] F']]; exact F'.
    + apply (Db x). { exact Bt. } exact Bb.
  - econstructor; intros.
    + exact WFp.
    + destruct I as [[] F]. apply union in F as [F | F]. { apply (NB x). { exact Bp. } exists tt. exact F. }
      apply (NB0 x). { apply BoundIn.TCaP. exact Bp. } exists tt. exact F.
    + apply NBo in B as []. exact Bp.
    + apply NBb in B as []. exact Bp.
    + apply NUo in U as []. exact Bp.
    + rewrite <- (BoundIn.term_iff body_if_match x). rewrite <- (UsedIn.term_iff body_if_match x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite <- (BoundIn.term_iff other_cases x). rewrite <- (UsedIn.term_iff other_cases x).
      repeat rewrite <- Map.in_overriding_union. reflexivity.
    + rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union.
    + rewrite <- (BoundIn.pattern_iff pattern x). apply Map.in_overriding_union.
    + eapply IHWF1. { intros. apply (NB0 x). { apply BoundIn.TCaO. exact B. } exact I. } intros x []. split.
      * intro F. apply Map.union_set in F as [F | F].
        -- apply union in F as [F | F]. 2: { right. exact F. }
           left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Uo. left. exists tt. exact F.
        -- left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Uo. right. apply Map.union_set in F as [F | F]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; assumption.
      * intro FF. apply Map.union_set. rewrite union. destruct FF as [F | F]. 2: { left. right. exact F. }
        eassert (I : Map.In _ _). { exists tt. exact F. } apply Uo in I as [[[] F'] | I]. { left. left. exact F'. }
        right. apply Map.union_set. destruct I as [B | U]; [left | right];
        [apply BoundIn.term_iff in B as [[] F'] | apply UsedIn.term_iff in U as [[] F']]; exact F'.
    + eapply context_superset; [eapply IHWF2 |]. { intros. apply (NB0 x). { apply BoundIn.TCaB. exact B. } exact I. } 2: {
        intros x [] F. apply Map.union_set. destruct (Cb x) as [[B | [[] F']] _]; [exists tt; exact F | left | right]. {
          apply BoundIn.pattern_iff in B as [[] B]. exact B. } exact F'. }
      intros x []. split.
      * intro F. apply Map.union_set in F as [F | F]. {
          left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
          apply Ub. left. apply BoundIn.pattern_iff. exists tt. exact F. }
        apply Map.union_set in F as [F | F].
        -- apply union in F as [F | F]. 2: { right. exact F. }
           left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Ub. right. apply Tb. left. exists tt. exact F.
        -- left. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
           apply Ub. right. apply Tb. right. apply Map.union_set in F as [F | F]; [left | right];
           [apply BoundIn.term_iff | apply UsedIn.term_iff]; exists tt; assumption.
      * intro FF. assert (E := Map.union_set); cbn in E; repeat rewrite E; clear E.
        rewrite union. destruct FF as [F | F]. 2: { right. left. right. exact F. }
        eassert (I : Map.In _ _). { exists tt. exact F. }
        apply Ub in I as [B | I]; [left | right]. { apply BoundIn.pattern_iff in B as [[] F']. exact F'. }
        apply Tb in I as [[[] F'] | I]; [left | right]. { left. exact F'. }
        destruct I as [B | U]; [left | right];
        [apply BoundIn.term_iff in B as [[] F'] | apply UsedIn.term_iff in U as [[] F']]; exact F'.
    + apply (Db x). { exact Bo. } exact Bb.
Qed.



(* TODO: make sure that bindings are disjoint: i.e., binding the same name implies that two terms are the same *)
Definition WellFormedContext context : Prop := (
  forall domain (D : Map.Domain context domain),
  Map.ForAll (fun _ => Unshadow.WellFormedIn domain) context) /\
  forall x1 y1 (F1 : Map.Find context x1 y1) x (B1 : BoundIn.Term y1 x)
  x2 y2 (F2 : Map.Find context x2 y2) (B2 : BoundIn.Term y2 x),
  y1 = y2.
Arguments WellFormedContext context/.

Definition WellFormedInContext context term : Prop :=
  WellFormedContext context /\ (* Yes, this `domain` is redundant, but efficiency doesn't matter, and this can be `destruct`ed *)
  forall domain (D : Map.Domain context domain),
  Unshadow.WellFormedIn domain term.
Arguments WellFormedInContext context term/.



Definition unshadow_context_each k v (acc : option (Map.set * Context.context)) : option (Map.set * Context.context) :=
  match acc with | None => None | Some (cant_bind, acc) =>
    match unshadow_reserve_bindings cant_bind v with None => None | Some (bindings, v') =>
      Some (Map.set_union bindings cant_bind, Map.overriding_add k v' acc)
    end
  end.
Arguments unshadow_context_each k v acc/.

Definition unshadow_context_acc :=
  Map.fold unshadow_context_each.
Arguments unshadow_context_acc/ acc context : rename.

Definition unshadow_context (context : Context.context) :=
  unshadow_context_acc (Some (Map.domain context, Map.empty)) context.
Arguments unshadow_context context/.

Lemma unfold_right {X Y} (f : X -> Y -> Y) init head tail
  : List.fold_right f init (head :: tail) = f head $ List.fold_right f init tail.
Proof. reflexivity. Qed.

Lemma unshadow_context_spec_acc
  {acc} (Ra : Reflect.Option (fun '(cant_bind', ctx) => Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx) acc) ctx
  : Reflect.Option (fun '(cant_bind', ctx') =>
      Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx /\
      Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx'
    ) $ unshadow_context_acc acc ctx.
Proof.
  unfold unshadow_context_acc. unfold Map.fold. rewrite MapCore.fold_spec. rewrite <- List.fold_left_rev_right.
  eapply (@Reflect.option_eq _ $ fun '(cant_bind', ctx') => (forall k v (F
    : SetoidList.InA MapCore.eq_key_elt (k, v) $ List.rev (MapCore.bindings ctx)), _) /\
      Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx'). {
    intros [cant_bind' ctx']. split; intros [H same]; (split; [| exact same]);
    intros k v F; apply (H k v); [apply -> SetoidList.InA_rev in F |];
    apply MapCore.bindings_spec1 in F; [| apply SetoidList.InA_rev in F]; exact F. }
  remember (List.rev (MapCore.bindings ctx)) as b eqn:Eb; clear ctx Eb.
  generalize dependent acc. induction b as [| [k v] tail IH]; intros. {
    cbn. destruct acc as [[bindings acc] |]; cbn in *; invert Ra; constructor. {
      split; intros k v F. { invert F. } eapply Y. exact F. }
    intros [cant_bind' ctx'] [C C']. apply (N (cant_bind', ctx')). exact C'. }
  rewrite unfold_right. simpl fst. simpl snd. unfold unshadow_context_each at 1. specialize (IH acc Ra).
  destruct IH as [[cant_bind' ctx'] [Y Y'] |]. 2: { constructor. intros [cant_bind' ctx'] [C C'].
    apply (N (cant_bind', ctx')). split. { intros k' v' F'. eapply C. right. exact F'. } exact C'. }
  destruct (wf_patterns_spec_bindings cant_bind' v) as [[cant_bind'' ctx''] [Y'' Y'''] |]; constructor. 2: {
    intros [cant_bind'' ctx''] [C C']. eapply (N (cant_bind'', v)). split; eapply C; left; split; reflexivity. }
  split; intros k' v' F'. { invert F'. { destruct H0. cbn in *. subst. exact Y''. } eapply Y. exact H0. }
  apply Map.overwrite_if_present_overwrite in F' as [[-> ->] | [N' F']]. { exact Y'''. } eapply Y'. exact F'.
Qed.

Lemma unshadow_context_spec ctx
  : Reflect.Option (fun '(cant_bind', ctx') =>
      Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx /\
      Map.ForAll (fun _ => WellFormed.AllPatternsIn) ctx'
    ) $ unshadow_context ctx.
Proof.
  unfold unshadow_context. eassert (A : _); [|
    destruct (@unshadow_context_spec_acc (Some (Map.domain ctx, Map.empty)) A ctx) as [[cant_bind' ctx'] [Y Y'] |]].
  - constructor. intros k v C. invert C.
  - constructor. split. { exact Y. } exact Y'.
  - constructor. intros [cant_bind' ctx'] [C C']. apply (N (cant_bind', ctx')). split. { exact C. } exact C'.
Qed.
