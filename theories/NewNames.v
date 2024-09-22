From LinearCore Require
  Map
  Name
  .
From LinearCore Require Import
  Invert
  .



Import Ascii.
Definition underscore := "_"%char.

Definition underscored name :=
  match name with
  | Name.Name head tail => Name.Name underscore (String.String head tail)
  end.



Definition in_ := @Map.in_.
Arguments in_/ {T} m k.

Axiom new_name : Map.set -> Name.name -> Name.name.
Arguments new_name reserved orig_name.
Extract Constant new_name =>
  "fun reserved -> let rec new_name' name = if in_ reserved name then new_name' (underscored name) else name in new_name'".

Axiom not_in_new_name : forall reserved orig_name (I : Map.In reserved (new_name reserved orig_name)), False.
Arguments not_in_new_name {reserved orig_name} I.

(* Yes, exactly equal, not just equivalent: *)
Axiom new_name_det : forall r1 r2 (E : Map.Eq r1 r2) orig_name, new_name r1 orig_name = new_name r2 orig_name.
Arguments new_name_det {r1 r2} E orig_name.



Definition generate_acc acc reserved : Map.set -> Map.to Name.name :=
  Map.fold (fun k _ acc => Map.overriding_add k (new_name (Map.set_union reserved (Map.domain acc)) k) acc) acc.
Arguments generate_acc acc reserved names/.

Definition generate : Map.set -> Map.set -> Map.to Name.name := generate_acc Map.empty.
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
  - right. destruct (Name.spec x k); subst; eexists; apply Map.find_overriding_add;
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
  destruct (Map.find_spec r2 k'). { apply Er in Y. apply N in Y as []. }
  repeat rewrite <- Map.find_iff. fold (Map.domain a2). repeat rewrite Map.find_domain.
  erewrite Map.in_eq. { reflexivity. } apply Map.eq_refl.
Qed.

Lemma generate_det {r1 r2} (Er : Map.Eq r1 r2) {n1 n2} (En : Map.Eq n1 n2)
  : generate r1 n1 = generate r2 n2.
Proof. apply generate_acc_det; try assumption. reflexivity. Qed.
