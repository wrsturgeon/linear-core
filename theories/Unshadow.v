From LinearCore Require
  NewNames
  Rename
  Term
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



Definition get_or_add m reserved k :=
  match Map.find m k with
  | Some v => (m, reserved, v)
  | None =>
      let v := NewNames.new_name reserved k in
      (Map.overriding_add k v m, Map.set_add v reserved, v)
  end.

Definition get_or_add_det {m1 r1 k1 m1' r1' v1} (E1 : get_or_add m1 r1 k1 = (m1', r1', v1))
  {m2} (Em : Map.Eq m1 m2)
  {r2} (Er : Map.Eq r1 r2)
  {k2} (Ek : k1 = k2)
  {m2' r2' v2} (E2 : get_or_add m2 r2 k2 = (m2', r2', v2))
  : Map.Eq m1' m2' /\ Map.Eq r1' r2' /\ v1 = v2.
Proof.
  subst. rename k2 into k. unfold get_or_add in *. destruct (Map.find_spec m1 k).
  - apply Em in Y. apply Map.find_iff in Y. rewrite Y in E2. clear Y. invert E1. invert E2.
    split. { exact Em. } split. { exact Er. } reflexivity.
  - destruct (Map.find_spec m2 k). { apply Em in Y. apply N in Y as []. }
    invert E1. invert E2. split. { split; intro F; apply Map.find_overriding_add;
      (apply Map.find_overriding_add in F as [[-> ->] | [Nf F]]; [left | right];
      [split; [reflexivity |]; apply NewNames.new_name_det |
        split; [exact Nf |]; apply Em; exact F ]); [| apply Map.eq_sym]; exact Er. }
    split. 2: { apply NewNames.new_name_det. exact Er. }
    split; intro F; apply Map.find_overriding_add; (
      apply Map.find_overriding_add in F as [[-> ->] | [Nf F]]; [left | right];
      [split; [| reflexivity]; apply NewNames.new_name_det |
        split; [| apply Er; exact F]; intros ->; apply Nf; apply NewNames.new_name_det]);
    try exact Er; apply Map.eq_sym; exact Er.
Qed.



Definition map3 {A B X Y} (f : X -> Y) (tuple : A * B * X) : A * B * Y :=
  match tuple with (a, b, x) => (a, b, f x) end.

(* NOTE: Even though it's a very unusual case, this has to return an option
 * because patterns (in `Cas`) can be ill-formed if they duplicate a binder. *)
Fixpoint unshadow_acc (acc : Map.to String.string) (reserved : Map.set) t :=
  match t with
  | Term.Ctr ctor => Some (acc, reserved, Term.Ctr ctor)
  | Term.Mov k => Some $ map3 Term.Mov (get_or_add acc reserved k)
  | Term.Ref k => Some $ map3 Term.Ref (get_or_add acc reserved k)
  | Term.App f a =>
      match unshadow_acc acc reserved f with None => None | Some (acc, reserved, f') =>
        match unshadow_acc acc reserved a with None => None | Some (acc, reserved, a') =>
          Some (acc, reserved, Term.App f' a')
        end
      end
  | Term.For variable type body =>
      match unshadow_acc acc reserved type with None => None | Some (acc, reserved, type') =>
        let variable' := NewNames.new_name reserved variable in
        let acc := Map.overwrite variable variable' acc in
        let reserved := Map.set_add variable' reserved in
        match unshadow_acc acc reserved body with None => None | Some (acc, reserved, body') =>
          Some (acc, reserved, Term.For variable' type' body')
        end
      end
  | Term.Cas pattern body_if_match other_cases =>
      match unshadow_acc acc reserved other_cases with None => None | Some (acc, reserved, other_cases') =>
        let bindings := BoundIn.pattern pattern in
        let rebindings := NewNames.generate reserved bindings in
        match Rename.pattern rebindings pattern with
        | None => None
        | Some pattern' =>
            let acc := Map.bulk_overwrite rebindings acc in
            let reserved := Map.set_union (Map.range rebindings) reserved in
            match unshadow_acc acc reserved body_if_match with None => None | Some (acc, reserved, body_if_match') =>
              Some (acc, reserved, Term.Cas pattern' body_if_match' other_cases')
            end
        end
      end
  end.

Definition unshadow reserved t :=
  match unshadow_acc (Map.to_self reserved) reserved t with
  | None => None
  | Some (_, used_in_unshadowed (* cool huh *), unshadowed) => Some unshadowed
  end.
Arguments unshadow reserved t/.



(* Rewriting without opening a can of worms: *)
Lemma unshadow_acc_for acc reserved variable type body
  : unshadow_acc acc reserved (Term.For variable type body) =
    match unshadow_acc acc reserved type with
    | None => None
    | Some (acc', reserved', type') =>
        match
          unshadow_acc
            (Map.overwrite variable (NewNames.new_name reserved' variable) acc')
            (Map.set_add (NewNames.new_name reserved' variable) reserved') body
        with
        | None => None
        | Some (acc'', reserved'', body') =>
            Some
              (acc'', reserved'',
              Term.For (NewNames.new_name reserved' variable) type' body')
        end
    end.
Proof. reflexivity. Qed.

Lemma unshadow_acc_cas acc reserved pattern body_if_match other_cases
  : unshadow_acc acc reserved (Term.Cas pattern body_if_match other_cases) =
    match unshadow_acc acc reserved other_cases with None => None | Some (acc, reserved, other_cases') =>
      match Rename.pattern (NewNames.generate reserved $ BoundIn.pattern pattern) pattern with
      | None => None
      | Some pattern' =>
          match
            unshadow_acc
              (Map.bulk_overwrite (NewNames.generate reserved $ BoundIn.pattern pattern) acc)
              (Map.set_union (Map.range (NewNames.generate reserved $ BoundIn.pattern pattern)) reserved)
              body_if_match
          with
          | None => None
          | Some (acc'', reserved'', body_if_match') =>
              Some (acc'', reserved'', Term.Cas pattern' body_if_match' other_cases')
          end
      end
    end.
Proof. cbn. reflexivity. Qed.

Variant Equiv : option (Map.to String.string * Map.set * Term.term) -> _ -> Prop :=
  | ENone
      : Equiv None None
  | ESome
      {acc1 acc2} (Eacc : Map.Eq acc1 acc2)
      {reserved1 reserved2} (Ereserved : Map.Eq reserved1 reserved2) output
      : Equiv (Some (acc1, reserved1, output)) (Some (acc2, reserved2, output))
  .

Lemma det_acc
  {a1 a2} (Ea : Map.Eq a1 a2)
  {r1 r2} (Er : Map.Eq r1 r2)
  {t1 t2} (Et : t1 = t2)
  : Equiv (unshadow_acc a1 r1 t1) (unshadow_acc a2 r2 t2).
Proof.
  subst. rename t2 into t. generalize dependent r2. generalize dependent r1.
  generalize dependent a2. generalize dependent a1. induction t; intros.
  - cbn. constructor; assumption.
  - cbn.
    destruct (get_or_add a1 r1 name) as [[a1'' r1''] t1] eqn:E1.
    destruct (get_or_add a2 r2 name) as [[a2'' r2''] t2] eqn:E2.
    destruct (get_or_add_det E1 Ea Er eq_refl E2) as [Ea'' [Er'' ->]].
    cbn. constructor; assumption.
  - cbn.
    destruct (get_or_add a1 r1 name) as [[a1'' r1''] t1] eqn:E1.
    destruct (get_or_add a2 r2 name) as [[a2'' r2''] t2] eqn:E2.
    destruct (get_or_add_det E1 Ea Er eq_refl E2) as [Ea'' [Er'' ->]].
    cbn. constructor; assumption.
  - cbn. destruct (IHt1 _ _ Ea _ _ Er). { constructor. }
    destruct (IHt2 _ _ Eacc _ _ Ereserved); constructor; eassumption.
  - repeat rewrite unshadow_acc_for. destruct (IHt1 _ _ Ea _ _ Er). { constructor. }
    assert (Ea' : Map.Eq
      (Map.overwrite variable (NewNames.new_name reserved1 variable) acc1)
      (Map.overwrite variable (NewNames.new_name reserved2 variable) acc2)). {
      split; intro F; apply Map.find_overriding_add;
      (apply Map.find_overriding_add in F as [[-> ->] | [N F]]; [left | right];
      [split; [reflexivity |]; apply NewNames.new_name_det |
        split; [exact N |]; apply Eacc; exact F]); [| apply Map.eq_sym]; exact Ereserved. }
    assert (Er' : Map.Eq
      (Map.set_add (NewNames.new_name reserved1 variable) reserved1)
      (Map.set_add (NewNames.new_name reserved2 variable) reserved2)). {
      split; intro F; apply Map.find_overriding_add;
      (apply Map.find_overriding_add in F as [[-> ->] | [N F]]; [left | right];
      [split; [| reflexivity]; apply NewNames.new_name_det | split; [| apply Ereserved; exact F];
        intros ->; apply N; apply NewNames.new_name_det]);
      try exact Ereserved; apply Map.eq_sym; exact Ereserved. }
    destruct (IHt2 _ _ Ea' _ _ Er'). { constructor. }
    erewrite NewNames.new_name_det; [constructor |]. { exact Eacc0. } { exact Ereserved0. } exact Ereserved.
  - repeat rewrite unshadow_acc_cas. destruct (IHt2 _ _ Ea _ _ Er). { constructor. }
    erewrite NewNames.generate_det. 2: { exact Ereserved. } 2: { apply Map.eq_refl. }
    eassert (O2O : Map.OneToOne $ NewNames.generate reserved2 (BoundIn.pattern pattern)). {
      apply NewNames.one_to_one_generate. } destruct (Rename.pattern_spec O2O pattern). 2: { constructor. }
    eassert (Ea' : Map.Eq
      (Map.bulk_overwrite (NewNames.generate reserved2 (BoundIn.pattern pattern)) acc1)
      (Map.bulk_overwrite (NewNames.generate reserved2 (BoundIn.pattern pattern)) acc2)). {
      split; intro F; apply Map.bulk_overwrite_bulk_overwrite; (
      apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]]; [left; exact F | right]);
      (split; [exact N |]); apply Eacc; exact F. }
    eassert (Eb' : Map.Eq
      (Map.set_union (Map.range (NewNames.generate reserved2 (BoundIn.pattern pattern))) reserved1)
      (Map.set_union (Map.range (NewNames.generate reserved2 (BoundIn.pattern pattern))) reserved2)). {
      split; intro F; (apply Map.union_overriding; [intros ? [] ? [] ?; reflexivity |]);
      (apply Map.union_overriding in F as [F | F]; [left; exact F | right | intros ? [] ? [] ?; reflexivity]);
      apply Ereserved; exact F. }
    destruct (IHt1 _ _ Ea' _ _ Eb'); constructor; eassumption.
Qed.

Lemma det
  {r1 r2} (Er : Map.Eq r1 r2)
  {t1 t2} (Et : t1 = t2)
  : unshadow r1 t1 = unshadow r2 t2.
Proof.
  eassert (A : Map.Eq (Map.to_self r1) (Map.to_self r2)).
  - split; intro F; apply Map.to_self_to_self; apply Map.to_self_to_self in F as [I ->];
    (split; [| reflexivity]); (eapply Map.in_eq; [| exact I]); [apply Map.eq_sym |]; exact Er.
  - unfold unshadow. destruct (det_acc A Er Et); reflexivity.
Qed.
