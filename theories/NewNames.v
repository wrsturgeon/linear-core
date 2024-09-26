From LinearCore Require
  Map
  .
From LinearCore Require Import
  Invert
  .



Definition in_ := @Map.in_.
Arguments in_/ {T} m k.

Import String.
Definition prime : String.string := "'".
Arguments prime/.

Axiom new_name : Map.set -> String.string -> String.string.
Arguments new_name reserved orig_name.
Extract Constant new_name =>
  "fun reserved -> let rec new_name' name = if in_ reserved name then new_name' (name ^ prime) else name in new_name'".

Axiom not_in_new_name : forall reserved orig_name (I : Map.In reserved (new_name reserved orig_name)), False.
Arguments not_in_new_name {reserved orig_name} I.

(* Yes, exactly equal, not just equivalent: *)
Axiom new_name_det : forall r1 r2 (E : Map.Eq r1 r2) orig_name, new_name r1 orig_name = new_name r2 orig_name.
Arguments new_name_det {r1 r2} E orig_name.



(* TODO: speed up by accumulating results of `range` call *)
Definition generate_acc acc reserved : Map.set -> Map.to String.string :=
  Map.fold (fun k _ acc => Map.overriding_add k (new_name (Map.set_union reserved (Map.range acc)) k) acc) acc.
Arguments generate_acc acc reserved names/.

Definition generate : Map.set -> Map.set -> Map.to String.string := generate_acc Map.empty.
Arguments generate reserved names/.



Lemma in_generate_acc acc reserved names k
  : Map.In (generate_acc acc reserved names) k <-> (Map.In names k \/ Map.In acc k).
Proof.
  cbn. unfold Map.fold. rewrite MapCore.fold_spec. assert (Iff
    : ((exists v, Map.Find names k v) \/ (exists v, Map.Find acc k v)) <->
      ((exists v, SetoidList.InA MapCore.eq_key_elt (k, v) (MapCore.bindings names)) \/ (exists v, Map.Find acc k v))). {
    split; (intros [[v F] | [v F]]; [left | right]; exists v; [| exact F]); apply MapCore.bindings_spec1; exact F. }
  rewrite Iff; clear Iff. remember (MapCore.bindings names) as b eqn:Eb; clear names Eb; rename b into names.
  generalize dependent k. generalize dependent reserved. generalize dependent acc.
  induction names as [| [k v] tail]; intros. {
    cbn. split. { intros [v F]. right. exists v. exact F. }
    intros [[v F] | [v F]]. 2: { exists v. exact F. } invert F. }
  rename k0 into x. cbn. rewrite IHtail; clear IHtail. split; intros [[y F] | [y F]].
  - left. exists y. right. exact F.
  - apply Map.find_overriding_add in F as [[-> ->] | [N F]]. 2: { right. exists y. exact F. }
    left. exists v. left. split; reflexivity.
  - invert F. 2: { left. eexists. eassumption. }
    destruct H0; cbn in *; subst. right. eexists. apply Map.find_overriding_add. left. split; reflexivity.
  - right. destruct (String.eqb_spec x k); subst; eexists; apply Map.find_overriding_add;
    [left | right]. { split; reflexivity. } split; eassumption.
Qed.

Lemma in_generate reserved names k
  : Map.In (generate reserved names) k <-> Map.In names k.
Proof.
  unfold generate. rewrite in_generate_acc. split. 2: { intro I. left. exact I. }
  intros [I | I]. { exact I. } destruct I as [v F]. invert F.
Qed.

Lemma not_in_generate_acc
  reserved x (R : Map.In reserved x)
  acc (N : forall k (R : Map.In reserved k) (A : Map.InRange acc k), False)
  names (G : Map.InRange (generate_acc acc reserved names) x)
  : False.
Proof.
  cbn in G. destruct G as [y G]. unfold Map.fold in G. rewrite MapCore.fold_spec in G.
  remember (MapCore.bindings names) as b eqn:Eb; clear names Eb; rename b into names.
  generalize dependent y. generalize dependent acc. generalize dependent x. generalize dependent reserved.
  induction names as [| [k v] tail]; intros. { cbn in *. destruct R. eapply N; eexists; eassumption. }
  simpl List.fold_left in G. apply IHtail in G as []; clear IHtail. { exact R. }
  intros z Rz I. destruct I as [z' F]. apply Map.find_overriding_add in F as [[-> ->] | [Nz F]].
  - eapply not_in_new_name. apply Map.in_overriding_union. left. exact Rz.
  - eapply N. { exact Rz. } eexists. exact F.
Qed.

Lemma not_in_generate
  reserved k (R : Map.In reserved k)
  names (G : Map.InRange (generate reserved names) k)
  : False.
Proof. eapply not_in_generate_acc; try eassumption. intros x I [y C]. invert C. Qed.

Lemma generate_acc_det {a1 a2} (Ea : a1 = a2) {r1 r2} (Er : Map.Eq r1 r2) {n1 n2} (En : Map.Eq n1 n2)
  : generate_acc a1 r1 n1 = generate_acc a2 r2 n2.
Proof.
  unfold generate_acc. unfold Map.fold. repeat rewrite MapCore.fold_spec. apply Map.bindings_eq in En.
  remember (MapCore.bindings n1) as b1 eqn:E1; clear n1 E1; rename b1 into n1.
  remember (MapCore.bindings n2) as b2 eqn:E2; clear n2 E2; rename b2 into n2.
  subst. rename n2 into names. generalize dependent r2. generalize dependent r1. generalize dependent a2.
  induction names as [| [k v] tail IH]; intros; cbn in *. { reflexivity. }
  erewrite IH; clear IH. 2: { exact Er. } erewrite new_name_det. { reflexivity. }
  intros k' v'. repeat rewrite Map.find_iff. repeat rewrite Map.find_overriding_union.
  destruct (Map.find_spec r1 k'). { apply Er in Y. apply Map.find_iff in Y. rewrite Y. reflexivity. }
  destruct (Map.find_spec r2 k'). { apply Er in Y. apply N in Y as []. } reflexivity.
Qed.

Lemma generate_det {r1 r2} (Er : Map.Eq r1 r2) {n1 n2} (En : Map.Eq n1 n2)
  : generate r1 n1 = generate r2 n2.
Proof. apply generate_acc_det; try assumption. reflexivity. Qed.

Lemma unfold_right {X Y} f (acc : Y) (hd : X) tl
  : List.fold_right f acc (List.cons hd tl) = f hd (List.fold_right f acc tl).
Proof. reflexivity. Qed.

Lemma unfold_left {X Y} f (acc : Y) (hd : X) tl
  : List.fold_left f (List.cons hd tl) acc = List.fold_left f tl (f acc hd).
Proof. reflexivity. Qed.

Theorem one_to_one_generate_acc {acc} (O2O : Map.OneToOne acc) reserved names
  : Map.OneToOne (generate_acc acc reserved names).
Proof.
  unfold generate_acc. unfold Map.fold. rewrite MapCore.fold_spec. assert (ND := MapCore.bindings_spec2w names).
  remember (MapCore.bindings names) as b eqn:Eb; clear names Eb; rename b into names.
  generalize dependent reserved. generalize dependent acc.
  induction ND as [| [head []] tail N ND IH]; intros. { simpl List.fold_left. exact O2O. }
  rewrite unfold_left. simpl fst. apply IH; clear IH.
  intro; intros. apply Map.find_overriding_add in F1 as [[-> ->] | [N1 F1]].
  - apply Map.find_overriding_add in F2 as [[-> _] | [N2 F2]]. { reflexivity. }
    eassert (IR : Map.InRange acc _). { eexists. exact F2. } apply Map.in_range in IR.
    eapply or_intror in IR. apply Map.in_overriding_union in IR. apply not_in_new_name in IR as [].
  - apply Map.find_overriding_add in F2 as [[-> ->] | [N2 F2]]. 2: { eapply O2O; eassumption. }
    eassert (IR : Map.InRange acc _). { eexists. exact F1. } apply Map.in_range in IR.
    eapply or_intror in IR. apply Map.in_overriding_union in IR. apply not_in_new_name in IR as [].
Qed.

Theorem one_to_one_generate reserved names
  : Map.OneToOne (generate reserved names).
Proof. apply one_to_one_generate_acc. apply Map.one_to_one_empty. Qed.
