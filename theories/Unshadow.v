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
Fixpoint unshadow_acc (acc : Map.to String.string) (reserved : Map.set) t :=
  match t with
  | Term.Ctr ctor => Some (reserved, Term.Ctr ctor)
  | Term.Mov k =>
      (* Have to supply a plan for any free variables (or they have to have been bound & added to the plan): *)
      match Map.find acc k with None => None | Some v => Some (reserved, Term.Mov v) end
  | Term.Ref k =>
      match Map.find acc k with None => None | Some v => Some (reserved, Term.Ref v) end
  | Term.App f a =>
      match unshadow_acc acc reserved f with None => None | Some (reserved, f') =>
        match unshadow_acc acc reserved a with None => None | Some (reserved, a') =>
          Some (reserved, Term.App f' a')
        end
      end
  | Term.For variable type body =>
      match unshadow_acc acc reserved type with None => None | Some (reserved, type') =>
        let variable' := NewNames.new_name reserved variable in
        let acc := Map.overwrite variable variable' acc in
        let reserved := Map.set_add variable' reserved in
        match unshadow_acc acc reserved body with None => None | Some (reserved, body') =>
          Some (reserved, Term.For variable' type' body')
        end
      end
  | Term.Cas pattern body_if_match other_cases =>
      match unshadow_acc acc reserved other_cases with None => None | Some (reserved, other_cases') =>
        let bindings := BoundIn.pattern pattern in
        let rebindings := NewNames.generate reserved bindings in
        match Rename.pattern rebindings pattern with
        | None => None
        | Some pattern' =>
            let acc := Map.bulk_overwrite rebindings acc in
            let reserved := Map.set_union (Map.range rebindings) reserved in
            match unshadow_acc acc reserved body_if_match with None => None | Some (reserved, body_if_match') =>
              Some (reserved, Term.Cas pattern' body_if_match' other_cases')
            end
        end
      end
  end.

Definition unshadow_reserve reserved t :=
  let generated := NewNames.generate reserved $ UsedIn.term t in
  option_map snd $ unshadow_acc generated (Map.set_union reserved $ Map.range generated) t.
Arguments unshadow_reserve reserved t/.

Definition unshadow := unshadow_reserve Map.empty.
Arguments unshadow/ t.



Variant Equiv : option (Map.set * Term.term) -> _ -> Prop :=
  | ENone
      : Equiv None None
  | ESome
      {reserved1 reserved2} (Ereserved : Map.Eq reserved1 reserved2) output
      : Equiv (Some (reserved1, output)) (Some (reserved2, output))
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
  - unfold unshadow_acc. destruct (Map.find_spec a1 name).
    + apply Ea in Y. apply Map.find_iff in Y. rewrite Y. constructor. exact Er.
    + destruct (Map.find_spec a2 name). { apply Ea in Y. apply N in Y as []. } constructor.
  - destruct (IHt1 _ _ Ea _ _ Er). { constructor. }
    destruct (IHt2 _ _ Ea _ _ Ereserved); constructor; eassumption.
  - destruct (IHt1 _ _ Ea _ _ Er). { constructor. } eassert (Ea' : _); [| eassert (Er' : _); [| destruct (IHt2
      (Map.overriding_add variable (NewNames.new_name reserved1 variable) a1)
      (Map.overriding_add variable (NewNames.new_name reserved2 variable) a2) Ea'
      (Map.overriding_add (NewNames.new_name reserved1 variable) tt reserved1)
      (Map.overriding_add (NewNames.new_name reserved2 variable) tt reserved2) Er')]]. 3: { constructor. }
    + split; intro F; apply Map.find_overriding_add; (apply Map.find_overriding_add in F as [[-> ->] | [N F]]; [left | right];
      [split; [reflexivity | apply NewNames.new_name_det] | split; [exact N |]; apply Ea; exact F]); [| apply Map.eq_sym]; exact Ereserved.
    + split; intro F; apply Map.find_overriding_add; (apply Map.find_overriding_add in F as [[-> ->] | [N F]]; [left | right];
      [split; [| reflexivity]; apply NewNames.new_name_det | split; [| apply Ereserved; exact F];
        intros ->; contradiction N; apply NewNames.new_name_det]); try exact Ereserved; apply Map.eq_sym; exact Ereserved.
    + erewrite NewNames.new_name_det. { constructor. exact Ereserved0. } exact Ereserved.
  - destruct (IHt2 _ _ Ea _ _ Er). { constructor. } destruct Rename.pattern eqn:ER. 2: {
      destruct Rename.pattern eqn:ER2 at 1. 2: { constructor. }
      eapply (Rename.pattern_iff (NewNames.one_to_one_generate _ _)) in ER2.
      eapply (@Rename.pattern_eq _ (NewNames.one_to_one_generate _ _)) in ER2; try reflexivity.
      * eapply Rename.pattern_iff in ER2. rewrite ER2 in ER. discriminate ER.
      * erewrite <- NewNames.generate_det. { apply Map.eq_refl. } { exact Ereserved. } apply Map.eq_refl. }
    apply (Rename.pattern_iff (NewNames.one_to_one_generate _ _)) in ER.
    eapply (@Rename.pattern_eq _ (NewNames.one_to_one_generate _ _)) in ER; try reflexivity; [
      eapply Rename.pattern_iff in ER; rewrite ER; clear ER |
      erewrite NewNames.generate_det; try apply Map.eq_refl; exact Ereserved].
    eassert (Ea' : _); [| eassert (Er' : _); [| destruct (IHt1
      (Map.overriding_union (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name
        (Map.overriding_union reserved1 $ Map.fold (fun _ v acc0 => Map.overriding_add v tt acc0) Map.empty acc) k) acc)
        Map.empty (BoundIn.pattern pattern)) a1)
      (Map.overriding_union (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name
        (Map.overriding_union reserved2 $ Map.fold (fun _ v acc0 => Map.overriding_add v tt acc0) Map.empty acc) k) acc)
        Map.empty (BoundIn.pattern pattern)) a2) Ea'
      (Map.overriding_union (Map.fold (fun _ v acc => Map.overriding_add v tt acc) Map.empty
        (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name (Map.overriding_union reserved1
          (Map.fold (fun _ v acc0 => Map.overriding_add v tt acc0) Map.empty acc)) k) acc)
          Map.empty (BoundIn.pattern pattern))) reserved1)
      (Map.overriding_union (Map.fold (fun _ v acc => Map.overriding_add v tt acc) Map.empty
        (Map.fold (fun k _ acc => Map.overriding_add k (NewNames.new_name (Map.overriding_union reserved2
          (Map.fold (fun _ v acc0 => Map.overriding_add v tt acc0) Map.empty acc)) k) acc)
          Map.empty (BoundIn.pattern pattern))) reserved2) Er')]]. 3: { constructor. }
    + assert (G := @NewNames.generate_det). cbn in G. erewrite G.
      * split; intro F; apply Map.bulk_overwrite_bulk_overwrite;
        (apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left; exact F | right]);
        (split; [intro I; apply N; exact I |]; apply Ea; exact F).
      * exact Ereserved.
      * apply Map.eq_refl.
    + assert (G := @NewNames.generate_det). cbn in G. erewrite G.
      * split; intro F; apply Map.bulk_overwrite_bulk_overwrite;
        (apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left; exact F | right]);
        (split; [intro I; apply N; exact I |]; apply Ereserved; exact F).
      * exact Ereserved.
      * apply Map.eq_refl.
    + constructor. exact Ereserved0. }
  Unshelve.
  - apply NewNames.one_to_one_generate.
  - apply NewNames.one_to_one_generate.
Qed.

Lemma det_reserve
  {r1 r2} (Er : Map.Eq r1 r2)
  {t1 t2} (Et : t1 = t2)
  : unshadow_reserve r1 t1 = unshadow_reserve r2 t2.
Proof.
  unfold unshadow_reserve.
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



Lemma bindings {acc reserved term bindings renamed}
  (E : unshadow_acc acc reserved term = Some (bindings, renamed))
  (prev : forall x y (Fa : Map.Find acc x y), Map.In reserved y)
  : Map.Reflect (fun x => BoundIn.Term renamed x \/ Map.In reserved x) bindings.
Proof.
  generalize dependent renamed. generalize dependent bindings.
  generalize dependent reserved. generalize dependent acc. induction term; intros; simpl unshadow_acc in *.
  - invert E. split. { intro I. right. exact I. }
    intros [B | I]. { invert B. } exact I.
  - destruct (Map.find_spec acc name) as [name' F | N]; invert E.
    split. { intro I. right. exact I. }
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



Lemma wf_spec acc reserved t
  : Reflect.Option
    (fun _ => WellFormed.AllPatternsIn t /\ forall x (U : UsedIn.Term t x), Map.In acc x)
    (unshadow_acc acc reserved t).
Proof.
  generalize dependent reserved. generalize dependent acc. induction t; intros; cbn in *.
  - constructor. split; intros. { constructor. } invert U.
  - destruct (Map.find_spec acc name); constructor.
    + split; intros. { constructor. } invert U. eexists. exact Y.
    + intros _ [_ C]. edestruct C. { constructor. } apply N in H as [].
  - destruct (Map.find_spec acc name); constructor.
    + split; intros. { constructor. } invert U. eexists. exact Y.
    + intros _ [_ C]. edestruct C. { constructor. } apply N in H as [].
  - destruct (IHt1 acc reserved) as [[r1 t1'] [WF1 IH1] |]. 2: {
      constructor. intros pair [WF C]. invert WF. apply N. { exact pair. }
      split. { exact APf. } intros. apply C. apply UsedIn.ApF. exact U. }
    destruct (IHt2 acc r1) as [[r2 t2'] [WF2 IH2] |]; constructor.
    + constructor. { constructor; assumption. } intros. invert U; [apply IH1 | apply IH2]; assumption.
    + intros pair [WF C]. invert WF. apply N. { exact pair. }
      split. { exact APa. } intros. apply C. apply UsedIn.ApA. exact U.
  - destruct (IHt1 acc reserved) as [[r1 t1'] [WF1 IH1] |]. 2: {
      constructor. intros pair [WF C]. invert WF. apply N. { exact pair. }
      split. { exact APt. } intros. apply C. apply UsedIn.FoT. exact U. }
    destruct (IHt2 (Map.overriding_add variable (NewNames.new_name r1 variable) acc)
      (Map.overriding_add (NewNames.new_name r1 variable) tt r1)) as [[r2 t2'] [WF2 IH2] |]; constructor.
    + split. { constructor; assumption. } intros. invert U. { apply IH1. exact used_in_type. }
      apply IH2 in used_in_body. apply Map.in_overriding_add in used_in_body as [-> | I]. 2: { exact I. }
      contradiction not_shadowed. reflexivity.
    + intros pair [WF C]. invert WF. apply N. { exact pair. }
      split. { exact APb. } intros. apply Map.in_overriding_add.
      destruct (String.eqb_spec x variable); [left | right]. { assumption. } apply C. apply UsedIn.FoB; assumption.
  - destruct (IHt2 acc reserved) as [[r2 t2'] [WF2 IH2] |]. 2: {
      constructor. intros pair [WF C]. invert WF. apply N. { exact pair. }
      split. { exact APo. } intros. apply C. apply UsedIn.CaO. exact U. }
    destruct (@Rename.pattern_spec (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name
      (Map.overriding_union r2 (Map.fold (fun _ v acc'' => Map.overriding_add v tt acc'') Map.empty acc'))
      k) acc') Map.empty (BoundIn.pattern pattern)) (NewNames.one_to_one_generate _ _) pattern). 2: {
      constructor. intros pair [WF C]. invert WF. eassert (RC : Rename.CompatiblePattern _ _). 2: {
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
        Map.empty (BoundIn.pattern pattern))) r2)) as [[r1 t1'] [WF1 IH1] |]; constructor.
    + constructor. { constructor; try assumption. invert RC; constructor. invert C; constructor; apply CS. }
      intros z U. invert U. 2: { apply IH2. exact used_in_another_case. } apply IH1 in used_in_body.
      apply Map.in_overriding_union in used_in_body as [I | I]. 2: { exact I. }
      apply NewNames.in_generate in I. apply BoundIn.pattern_iff in I. apply not_shadowed in I as [].
    + intros pair [WF C]. invert WF. apply N. { exact pair. } split. { exact APb. } intros.
      apply Map.in_overriding_union. destruct (BoundIn.pattern_spec pattern x0); [left | right].
      * apply NewNames.in_generate. apply BoundIn.pattern_iff. exact Y0.
      * apply C. apply UsedIn.CaB; assumption.
Qed.

Lemma disjoint_used {acc reserved term reserved' renamed}
  (E : unshadow_acc acc reserved term = Some (reserved', renamed))
  (prev : forall x y (Fa : Map.Find acc x y), Map.In reserved y)
  {y} (I : Map.In reserved y) (U : UsedIn.Term renamed y)
  : exists x, Map.Find acc x y.
Proof.
  generalize dependent y. generalize dependent renamed. generalize dependent reserved'.
  generalize dependent reserved. generalize dependent acc. induction term; intros; cbn in *.
  - invert E. invert U.
  - destruct (Map.find_spec acc name); invert E. invert U. eexists. exact Y.
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

Lemma disjoint_bound {acc reserved term reserved' renamed}
  (E : unshadow_acc acc reserved term = Some (reserved', renamed))
  (prev : forall x y (Fa : Map.Find acc x y), Map.In reserved y)
  {x} (I : Map.In reserved x) (B : BoundIn.Term renamed x)
  : False.
Proof.
  generalize dependent x. generalize dependent renamed. generalize dependent reserved'.
  generalize dependent reserved. generalize dependent acc. induction term; intros; cbn in *.
  - invert E. invert B.
  - destruct (Map.find_spec acc name); invert E. invert B.
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

Lemma used_reserved {acc reserved term reserved' renamed}
  (E : unshadow_acc acc reserved term = Some (reserved', renamed))
  (prev : forall x y (Fa : Map.Find acc x y), Map.In reserved y)
  {x} (U : UsedIn.Term renamed x)
  : Map.In reserved' x.
Proof.
  generalize dependent x. generalize dependent renamed. generalize dependent reserved'.
  generalize dependent reserved. generalize dependent acc. induction term; intros; cbn in *.
  - invert E. invert U.
  - destruct (Map.find_spec acc name); invert E. invert U. eapply prev. exact Y.
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



Inductive Unshadowed : Term.term -> Prop :=
  | Ctr ctor
      : Unshadowed (Term.Ctr ctor)
  | Mov name
      : Unshadowed (Term.Mov name)
  | Ref name
      : Unshadowed (Term.Ref name)
  | App
      {function} (Uf : Unshadowed function)
      {argument} (Ua : Unshadowed argument)
      (disj_f_a : forall x (Bf : BoundIn.Term function x) (Ua : UsedIn.Term argument x), False)
      (disj_a_f : forall x (Ba : BoundIn.Term argument x) (Uf : UsedIn.Term function x), False)
      : Unshadowed (Term.App function argument)
  | For
      {type} (Ut : Unshadowed type)
      {body} (Ub : Unshadowed body)
      (disj_t_b : forall x (Bt : BoundIn.Term type x) (Ub : UsedIn.Term body x), False)
      (disj_b_t : forall x (Bb : BoundIn.Term body x) (Ut : UsedIn.Term type x), False) {variable}
      (Nt : forall (B : BoundIn.Term type variable), False)
      (Nb : forall (B : BoundIn.Term body variable), False)
      : Unshadowed (Term.For variable type body)
  | Cas
      {body_if_match} (Ub : Unshadowed body_if_match)
      {other_cases} (Uo : Unshadowed other_cases)
      (disj_b_o : forall x (Bb : BoundIn.Term body_if_match x) (Uo : UsedIn.Term other_cases x), False)
      (disj_o_b : forall x (Bo : BoundIn.Term other_cases x) (Ub : UsedIn.Term body_if_match x), False) {pattern}
      (Nb : forall x (Bp : BoundIn.Pattern pattern x) (Bt : BoundIn.Term body_if_match x), False)
      (No : forall x (Bp : BoundIn.Pattern pattern x) (Bo : BoundIn.Term other_cases x), False)
      : Unshadowed (Term.Cas pattern body_if_match other_cases)
  .

Lemma on_the_tin_acc {acc reserved t reserved' renamed}
  (E : unshadow_acc acc reserved t = Some (reserved', renamed))
  (prev : forall x y (Fa : Map.Find acc x y), Map.In reserved y)
  : Unshadowed renamed.
Proof.
  generalize dependent renamed. generalize dependent reserved'.
  generalize dependent reserved. generalize dependent acc. induction t; intros; cbn in *.
  - invert E. constructor.
  - destruct (Map.find_spec acc name); cbn in E; invert E; constructor.
  - destruct (Map.find_spec acc name); cbn in E; invert E; constructor.
  - destruct unshadow_acc as [[reserved1 renamed1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[reserved2 renamed2] |] eqn:E2 in E; invert E.
    specialize (IHt1 _ _ prev _ _ E1). eassert (prev' : _); [| specialize (IHt2 _ _ prev' _ _ E2)]. {
      intros. eapply bindings. { exact E1. } { exact prev. } right. eapply prev. exact Fa. }
    constructor; try assumption; intros.
    + eapply disjoint_bound; try exact Bf; try eassumption.
      assert (I : Map.In reserved1 x). { eapply bindings. { exact E1. } { exact prev. } left. exact Bf. }
      destruct (disjoint_used E2 prev' I Ua) as [z F]. eapply prev. exact F.
    + eapply disjoint_bound; try exact Ba; try eassumption.
      eapply used_reserved. 3: { exact Uf. } { eassumption. } exact prev.
  - destruct unshadow_acc as [[reserved1 renamed1] |] eqn:E1 in E. 2: { discriminate E. }
    destruct unshadow_acc as [[reserved2 renamed2] |] eqn:E2 in E; invert E.
    specialize (IHt1 _ _ prev _ _ E1). eassert (prev' : _); [| specialize (IHt2 _ _ prev' _ _ E2)]. {
      intros. apply Map.in_overriding_add. apply Map.find_overriding_add in Fa as [[-> ->] | [Na Fa]]. { left. reflexivity. }
      right. eapply bindings. { exact E1. } { exact prev. } right. eapply prev. exact Fa. }
    constructor; try assumption; intros.
    + eapply disjoint_bound; try exact Bt; try eassumption.
      assert (I : Map.In reserved1 x). { eapply bindings. { exact E1. } { exact prev. } left. exact Bt. }
      eassert (I' : _); [| destruct (disjoint_used E2 prev' I' Ub) as [z F]]. { apply Map.in_overriding_add. right. exact I. }
      apply Map.find_overriding_add in F as [[-> ->] | [N F]]. { apply NewNames.not_in_new_name in I as []. } eapply prev. exact F.
    + eapply disjoint_bound; try exact Ba; try eassumption. apply Map.in_overriding_add.
      destruct (String.eqb_spec x (NewNames.new_name reserved1 variable)); [left | right]. { assumption. }
      eapply used_reserved. 3: { exact Ut. } { eassumption. } exact prev.
    + eapply NewNames.not_in_new_name. eapply bindings. 3: { left. exact B. } { eassumption. } exact prev.
    + eapply disjoint_bound. { exact E2. } { exact prev'. } 2: { exact B. } apply Map.in_overriding_add. left. reflexivity.
  - destruct unshadow_acc as [[reserved2 renamed2] |] eqn:E2 in E. 2: { discriminate E. }
    destruct (@Rename.pattern_spec (Map.fold (fun k _ acc' => Map.overriding_add k (NewNames.new_name
      (Map.overriding_union reserved2 (Map.fold (fun _ v acc'' => Map.overriding_add v tt acc'') Map.empty acc'))
      k) acc') Map.empty (BoundIn.pattern pattern)) (NewNames.one_to_one_generate _ _) pattern). 2: { discriminate E. }
    destruct unshadow_acc as [[reserved1 renamed1] |] eqn:E1 in E; invert E.
    specialize (IHt2 _ _ prev _ _ E2). eassert (prev' : _); [| specialize (IHt1 _ _ prev' _ _ E1)]. {
      intros k v F. apply Map.in_overriding_union. rewrite Map.in_range.
      apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. { left. eexists. exact F. }
      right. eapply bindings. { exact E2. } { exact prev. } right. eapply prev. exact F. }
    constructor; try assumption; intros.
    + eapply disjoint_bound; try exact Bb; try eassumption. apply Map.in_overriding_union. rewrite Map.in_range.
      right. eapply used_reserved. { eassumption. } { exact prev. } exact Uo.
    + eapply disjoint_bound; try exact Bo; try eassumption.
      assert (I : Map.In reserved2 x0). { eapply bindings. { exact E2. } { exact prev. } left. exact Bo. }
      eassert (I' : _); [| destruct (disjoint_used E1 prev' I' Ub) as [z F]]. { apply Map.in_overriding_union. right. exact I. }
      apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]. 2: { eapply prev. exact F. }
      eassert (IR : Map.InRange _ _). { eexists. exact F. } eapply NewNames.not_in_generate in IR as []. exact I.
    + apply (Rename.bound_in_pattern Y) in Bp as [z [B F]].
      eapply disjoint_bound. { exact E1. } { exact prev'. } 2: { exact Bt. }
      apply Map.in_overriding_union. left. apply Map.in_range. eexists. exact F.
    + apply (Rename.bound_in_pattern Y) in Bp as [z [B F]].
      eapply NewNames.not_in_generate. 2: { eexists. exact F. }
      eapply bindings. 3: { left. exact Bo. } { exact E2. } exact prev.
Qed.

Lemma on_the_tin_reserve {reserved t renamed} (E : unshadow_reserve reserved t = Some renamed)
  : Unshadowed renamed.
Proof.
  cbn in E. destruct unshadow_acc as [[? ?] |] eqn:Ea; invert E. eapply on_the_tin_acc in Ea. { exact Ea. }
  intros k v F. apply Map.in_overriding_union. right. rewrite Map.in_range. eexists. exact F.
Qed.

Lemma on_the_tin {t renamed} (E : unshadow t = Some renamed)
  : Unshadowed renamed.
Proof. apply on_the_tin_reserve in E. exact E. Qed.



Fixpoint unshadowed_acc t :=
  match t with
  | Term.Ctr _ =>
      Some (Map.empty, Map.empty)
  | Term.Mov name
  | Term.Ref name =>
      Some (Map.empty, Map.singleton name tt)
  | Term.App function argument =>
      match unshadowed_acc function with None => None | Some (bound_in_function, used_in_function) =>
      match unshadowed_acc argument with None => None | Some (bound_in_argument, used_in_argument) =>
      if andb
        (Map.disjoint bound_in_function used_in_argument)
        (Map.disjoint bound_in_argument used_in_function)
      then Some (
        Map.set_union bound_in_function bound_in_argument,
        Map.set_union used_in_argument used_in_function)
      else None end end
  | Term.For variable type body =>
      match unshadowed_acc type with None => None | Some (bound_in_type, used_in_type) =>
      match unshadowed_acc body with None => None | Some (bound_in_body, used_in_body) =>
      if
        andb (Map.disjoint bound_in_type used_in_body) $
        andb (Map.disjoint bound_in_body used_in_type) $
        andb (negb $ Map.in_ bound_in_type variable) $ negb $ Map.in_ bound_in_body variable
      then Some (
        Map.set_add variable $ Map.set_union bound_in_type bound_in_body,
        Map.set_union used_in_type $ Map.remove variable used_in_body)
      else None end end
  | Term.Cas pattern body_if_match other_cases =>
      match unshadowed_acc body_if_match with None => None | Some (bound_in_body_if_match, used_in_body_if_match) =>
      match unshadowed_acc other_cases with None => None | Some (bound_in_other_cases, used_in_other_cases) =>
      let bound_in_pattern := BoundIn.pattern pattern in
      if
        andb (Map.disjoint bound_in_body_if_match used_in_other_cases) $
        andb (Map.disjoint bound_in_other_cases used_in_body_if_match) $
        andb (Map.disjoint bound_in_pattern bound_in_body_if_match) $
        Map.disjoint bound_in_pattern bound_in_other_cases
      then Some (
        Map.set_union bound_in_pattern $ Map.set_union bound_in_body_if_match bound_in_other_cases,
        Map.set_union used_in_other_cases $ Map.minus used_in_body_if_match bound_in_pattern)
      else None end end
  end.

Definition unshadowed t := match unshadowed_acc t with None => false | Some _ => true end.
Arguments unshadowed t/.

Lemma unshadowed_acc_bound_used {t bound used} (E : unshadowed_acc t = Some (bound, used))
  : Map.Reflect (BoundIn.Term t) bound /\ Map.Reflect (UsedIn.Term t) used.
Proof.
  generalize dependent used. generalize dependent bound. induction t; intros; cbn in *.
  - invert E. split; intros.
    + split. { intro I. apply Map.empty_empty in I as []. } intro B. invert B.
    + split. { intro I. apply Map.empty_empty in I as []. } intro B. invert B.
  - invert E. split; intros.
    + split. { intro I. apply Map.empty_empty in I as []. } intro B. invert B.
    + split. { intro I. apply Map.in_singleton in I as ->. constructor. }
      intro U. invert U. apply Map.in_singleton. reflexivity.
  - invert E. split; intros.
    + split. { intro I. apply Map.empty_empty in I as []. } intro B. invert B.
    + split. { intro I. apply Map.in_singleton in I as ->. constructor. }
      intro U. invert U. apply Map.in_singleton. reflexivity.
  - destruct unshadowed_acc as [[bound_in_function used_in_function] |] eqn:Ef in E. 2: { discriminate E. }
    destruct unshadowed_acc as [[bound_in_argument used_in_argument] |] eqn:Ea in E. 2: { discriminate E. }
    assert (D := @Map.disjoint_spec unit unit). cbn in D.
    destruct (D bound_in_function used_in_argument). 2: { discriminate E. }
    destruct (D bound_in_argument used_in_function); invert E. clear D.
    specialize (IHt1 _ _ Ef) as [Bf Uf]. specialize (IHt2 _ _ Ea) as [Ba Ua]. split; intros.
    + split.
      * intro I. apply Map.in_overriding_union in I as [I | I].
        -- apply BoundIn.TApF. apply Bf. exact I.
        -- apply BoundIn.TApA. apply Ba. exact I.
      * intro B. apply Map.in_overriding_union. invert B; [left | right].
        -- apply Bf. exact bound_in_function0.
        -- apply Ba. exact bound_in_argument0.
    + split.
      * intro I. apply Map.in_overriding_union in I as [I | I].
        -- apply UsedIn.ApA. apply Ua. exact I.
        -- apply UsedIn.ApF. apply Uf. exact I.
      * intro B. apply Map.in_overriding_union. invert B; [right | left].
        -- apply Uf. exact used_in_function0.
        -- apply Ua. exact used_in_argument0.
  - destruct unshadowed_acc as [[bound_in_type used_in_type] |] eqn:Et in E. 2: { discriminate E. }
    destruct unshadowed_acc as [[bound_in_body used_in_body] |] eqn:Eb in E. 2: { discriminate E. }
    assert (D := @Map.disjoint_spec unit unit). cbn in D.
    destruct (D bound_in_type used_in_body). 2: { discriminate E. }
    destruct (D bound_in_body used_in_type). 2: { discriminate E. } clear D.
    assert (I := @Map.in_spec unit). cbn in I.
    destruct (I bound_in_type variable). { discriminate E. }
    destruct (I bound_in_body variable); invert E. clear I.
    specialize (IHt1 _ _ Et) as [Bt Ut]. specialize (IHt2 _ _ Eb) as [Bb Ub]. split; intros.
    + split.
      * intro I. apply Map.in_overriding_add in I as [-> | I]. { constructor. }
        apply Map.in_overriding_union in I as [I | I]. { apply BoundIn.TFoT. apply Bt. exact I. }
        apply BoundIn.TFoB. apply Bb. exact I.
      * intro B. apply Map.in_overriding_add. invert B; [left; reflexivity | |];
        right; apply Map.in_overriding_union; [left | right]. { apply Bt. exact bound_in_type0. }
        apply Bb. exact bound_in_body0.
    + split.
      * intro I. apply Map.in_overriding_union in I as [I | I]. { apply UsedIn.FoT. apply Ut. exact I. }
        eapply Map.in_remove_if_present in I as [Nx I]. 2: { apply Map.remove_if_present_remove. }
        apply UsedIn.FoB. { exact Nx. } apply Ub. exact I.
      * intro U. apply Map.in_overriding_union. invert U; [left | right]. { apply Ut. exact used_in_type0. }
        eapply Map.in_remove_if_present. { apply Map.remove_if_present_remove. }
        split. { exact not_shadowed. } apply Ub. exact used_in_body0.
  - destruct unshadowed_acc as [[bound_in_body_if_match used_in_body_if_match] |] eqn:Eb in E. 2: { discriminate E. }
    destruct unshadowed_acc as [[bound_in_other_cases used_in_other_cases] |] eqn:Eo in E. 2: { discriminate E. }
    assert (D := @Map.disjoint_spec unit unit). cbn in D.
    destruct (D bound_in_body_if_match used_in_other_cases). 2: { discriminate E. }
    destruct (D bound_in_other_cases used_in_body_if_match). 2: { discriminate E. }
    destruct (D (BoundIn.pattern pattern) bound_in_body_if_match). 2: { discriminate E. }
    destruct (D (BoundIn.pattern pattern) bound_in_other_cases); invert E. clear D.
    specialize (IHt1 _ _ Eb) as [Bb Ub]. specialize (IHt2 _ _ Eo) as [Bo Uo]. split; intros.
    + split.
      * intro I. apply Map.in_overriding_union in I as [I | I]. { apply BoundIn.TCaP. apply BoundIn.pattern_iff. exact I. }
        apply Map.in_overriding_union in I as [I | I]. { apply BoundIn.TCaB. apply Bb. exact I. }
        apply BoundIn.TCaO. apply Bo. exact I.
      * intro B. apply Map.in_overriding_union. invert B; [left; apply BoundIn.pattern_iff; exact bound_in_pattern | |];
        right; apply Map.in_overriding_union; [left | right]. { apply Bb. exact bound_in_body. }
        apply Bo. exact bound_in_another_case.
    + split.
      * intro I. apply Map.in_overriding_union in I as [I | [y F]]. { apply UsedIn.CaO. apply Uo. exact I. }
        apply Map.minus_minus in F as [F N]. apply UsedIn.CaB. 2: { apply Ub. eexists. exact F. }
        intro B. apply N. apply BoundIn.pattern_iff. exact B.
      * intro U. apply Map.in_overriding_union. invert U; [right | left]. 2: { apply Uo. exact used_in_another_case. }
        apply Ub in used_in_body as [y F]. eexists. apply Map.minus_minus. split. { exact F. }
        intro B. apply not_shadowed. apply BoundIn.pattern_iff. exact B.
Qed.

Lemma unshadowed_spec t
  : Reflect.Bool (Unshadowed t) (unshadowed t).
Proof.
  induction t; cbn in *.
  - constructor. constructor.
  - constructor. constructor.
  - constructor. constructor.
  - destruct unshadowed_acc as [[bound_in_function used_in_function] |] eqn:Ef; invert IHt1. 2: {
      constructor. intro U. apply N. invert U. exact Uf. }
    destruct unshadowed_acc as [[bound_in_argument used_in_argument] |] eqn:Ea at 1; rewrite Ea in IHt2; invert IHt2. 2: {
      constructor. intro U. apply N. invert U. exact Ua. }
    destruct (unshadowed_acc_bound_used Ef) as [Bf Uf]. destruct (unshadowed_acc_bound_used Ea) as [Ba Ua].
    assert (D := @Map.disjoint_spec unit unit). cbn in D. destruct (D bound_in_function used_in_argument). 2: {
      constructor. intro C. invert C. apply N. intros. eapply disj_f_a. { apply Bf. exact Ma. } apply Ua. exact Mb. }
    destruct (D bound_in_argument used_in_function); constructor. 2: {
      intro C. invert C. apply N. intros. eapply disj_a_f. { apply Ba. exact Ma. } apply Uf. exact Mb. }
    constructor. { exact Y. } { exact Y0. } { intros. eapply Y1. { apply Bf. exact Bf0. } apply Ua. exact Ua0. }
    intros. eapply Y2. { apply Ba. exact Ba0. } apply Uf. exact Uf0.
  - destruct unshadowed_acc as [[bound_in_type used_in_type] |] eqn:Et; invert IHt1. 2: {
      constructor. intro U. apply N. invert U. exact Ut. }
    destruct unshadowed_acc as [[bound_in_body used_in_body] |] eqn:Eb at 1; rewrite Eb in IHt2; invert IHt2. 2: {
      constructor. intro U. apply N. invert U. exact Ub. }
    destruct (unshadowed_acc_bound_used Et) as [Bt Ut]. destruct (unshadowed_acc_bound_used Eb) as [Bb Ub].
    assert (D := @Map.disjoint_spec unit unit). cbn in D. destruct (D bound_in_type used_in_body). 2: {
      constructor. intro C. invert C. apply N. intros. eapply disj_t_b. { apply Bt. exact Ma. } apply Ub. exact Mb. }
    destruct (D bound_in_body used_in_type). 2: {
      constructor. intro C. invert C. apply N. intros. eapply disj_b_t. { apply Bb. exact Ma. } apply Ut. exact Mb. }
    clear D. assert (I := @Map.in_spec unit). cbn in I. destruct (I bound_in_type variable). {
      constructor. intro C. invert C. apply Nt. apply Bt. exact Y3. }
    destruct (I bound_in_body variable); constructor. { intro C. invert C. apply Nb. apply Bb. exact Y3. }
    constructor. { exact Y. } { exact Y0. } { intros. eapply Y1. { apply Bt. exact Bt0. } apply Ub. exact Ub0. }
    { intros. eapply Y2. { apply Bb. exact Bb0. } apply Ut. exact Ut0. } { intro B. apply N. apply Bt. exact B. }
    intro B. apply N0. apply Bb. exact B.
  - destruct unshadowed_acc as [[bound_in_body_if_match used_in_body_if_match] |] eqn:Eb; invert IHt1. 2: {
      constructor. intro U. apply N. invert U. exact Ub. }
    destruct unshadowed_acc as [[bound_in_other_cases used_in_other_cases] |] eqn:Eo at 1; rewrite Eo in IHt2; invert IHt2. 2: {
      constructor. intro U. apply N. invert U. exact Uo. }
    destruct (unshadowed_acc_bound_used Eb) as [Bb Ub]. destruct (unshadowed_acc_bound_used Eo) as [Bo Uo].
    assert (D := @Map.disjoint_spec unit unit). cbn in D. destruct (D bound_in_body_if_match used_in_other_cases). 2: {
      constructor. intro C. invert C. apply N. intros. eapply disj_b_o. { apply Bb. exact Ma. } apply Uo. exact Mb. }
    destruct (D bound_in_other_cases used_in_body_if_match). 2: {
      constructor. intro C. invert C. apply N. intros. eapply disj_o_b. { apply Bo. exact Ma. } apply Ub. exact Mb. }
    destruct (D (BoundIn.pattern pattern) bound_in_body_if_match). 2: {
      constructor. intro C. invert C. eapply N. intros. eapply Nb. { apply BoundIn.pattern_iff. exact Ma. } apply Bb. exact Mb. }
    destruct (D (BoundIn.pattern pattern) bound_in_other_cases); constructor. 2: {
      intro C. invert C. eapply N. intros. eapply No. { apply BoundIn.pattern_iff. exact Ma. } apply Bo. exact Mb. }
    constructor; intros. { exact Y. } { exact Y0. } { eapply Y1. { apply Bb. exact Bb0. } apply Uo. exact Uo0. }
    + eapply Y2. { apply Bo. exact Bo0. } apply Ub. exact Ub0.
    + eapply Y3. { apply BoundIn.pattern_iff. exact Bp. } apply Bb. exact Bt.
    + eapply Y4. { apply BoundIn.pattern_iff. exact Bp. } apply Bo. exact Bo0.
Qed.

Lemma unshadowed_iff t
  : Unshadowed t <-> unshadowed t = true.
Proof. exact (Reflect.bool_iff (unshadowed_spec _)). Qed.



(* sanity check that no information is destroyed: *)
(*
Fixpoint without_scope := ...
Lemma invert := (E : unshadow s t = Some t')
  : without_scope (Map.invert s) t' = t.
*)
