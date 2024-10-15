From Coq Require Import
  Ascii
  String
  .
From Equations Require Import
  Equations
  .
From LinearCore Require
  Map
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



Definition prime : String.string := "'".
Arguments prime/.

Definition next s : string := s ++ "'".
Arguments next s/.

Fixpoint prefix short long :=
  match short with EmptyString => true | String head tail =>
    match long with EmptyString => false | String head' tail' =>
      andb (Ascii.eqb head head') $ prefix tail tail'
    end
  end.

Lemma prefix_refl x
  : prefix x x = true.
Proof.
  induction x; cbn in *. { reflexivity. } rewrite Ascii.eqb_refl. rewrite IHx. reflexivity.
Qed.

Lemma prefix_prime x
  : prefix (x ++ "'") x = false.
Proof. induction x; cbn in *. { reflexivity. } rewrite Ascii.eqb_refl; cbn. exact IHx. Qed.

Fixpoint remove_prefix short long :=
  match short with EmptyString => Some long | String head tail =>
    match long with EmptyString => None | String head' tail' =>
      if Ascii.eqb head head' then remove_prefix tail tail' else None
    end
  end.

Lemma prefix_remove short long
  : prefix short long = true <-> exists overflow, remove_prefix short long = Some overflow.
Proof.
  generalize dependent long. induction short; intros; cbn in *. { split. { eexists. reflexivity. } reflexivity. }
  destruct long. { split. { intro D. discriminate D. } intros [? D]. discriminate D. }
  destruct (Ascii.eqb_spec a a0); subst; cbn in *. { apply IHshort. }
  split. { intro D. discriminate D. } intros [? D]. discriminate D.
Qed.

Lemma prefix_acc a b (E : prefix (a ++ "'") b = true)
  : prefix a b = true.
Proof.
  generalize dependent b. induction a as [| xa a IH]; intros; cbn in *. { destruct b; reflexivity. }
  destruct b as [| xb b]. { discriminate E. } destruct (Ascii.eqb_spec xa xb); subst; cbn in *. 2: { discriminate E. }
  apply IH. exact E.
Qed.

Definition count_acc acc (f : _ -> bool) {T} : Map.to T -> nat := Map.fold (fun x _ => if f x then S else id) acc.
Arguments count_acc acc f {T}/ m.

Definition count := @count_acc 0.
Arguments count/ f {T} m.

(*
Lemma pull_out_of_acc acc f {T} (m : Map.to T)
  : count_acc acc f m = acc + count f m.
Proof.
  cbn. unfold Map.fold. repeat rewrite MapCore.fold_spec. remember (MapCore.bindings m) as b eqn:Eb; clear m Eb.
  generalize dependent acc. induction b as [| [k v] tail IH]; intros; cbn in *. { symmetry. apply PeanoNat.Nat.add_0_r. }
  repeat rewrite (IH $ _ _). rewrite PeanoNat.Nat.add_assoc. f_equal.
  destruct f. { symmetry. apply PeanoNat.Nat.add_1_r. } unfold id. symmetry. apply PeanoNat.Nat.add_0_r.
Qed.
*)

Lemma pull_out_of_acc acc orig_name {T} (li : list (_ * T))
  : List.fold_left (fun a kv => (if prefix orig_name (fst kv) then S else id) a) li acc =
    acc + List.fold_left (fun a kv => (if prefix orig_name (fst kv) then S else id) a) li 0.
Proof.
  generalize dependent orig_name. generalize dependent acc.
  induction li as [| [k v] tail IH]; intros; cbn in *. { symmetry. apply PeanoNat.Nat.add_0_r. }
  repeat rewrite (IH $ _ _). rewrite PeanoNat.Nat.add_assoc. f_equal.
  destruct prefix. { symmetry. apply PeanoNat.Nat.add_1_r. } unfold id. symmetry. apply PeanoNat.Nat.add_0_r.
Qed.

Lemma le_prime x {T} (tail : list (_ * T))
  : List.fold_left (fun a kv => (if prefix (x ++ "'") $ fst kv then S else id) a) tail 0 < S $
    List.fold_left (fun a kv => (if prefix  x         $ fst kv then S else id) a) tail 0.
Proof.
  generalize dependent x. induction tail as [| [k v] tail IH]; intros; cbn in *. { constructor. }
  repeat rewrite (pull_out_of_acc $ _ _). rewrite <- PeanoNat.Nat.add_succ_l.
  destruct (prefix (x ++ "'") k) eqn:Ep'. { apply prefix_acc in Ep' as ->. cbn. apply -> PeanoNat.Nat.succ_lt_mono. apply IH. }
  unfold id at 1. rewrite PeanoNat.Nat.add_0_l. destruct (prefix x k) eqn:Ep; cbn in *. 2: { apply IH. }
  eapply PeanoNat.Nat.lt_trans. { apply IH. } apply -> PeanoNat.Nat.succ_lt_mono. apply PeanoNat.Nat.lt_succ_diag_r.
Qed.

Equations new_name (reserved : Map.set) (orig_name : string)
  : string by wf (count (prefix orig_name) reserved) lt :=
  new_name reserved orig_name with Map.found_dec reserved orig_name => {
    | Map.NotFound => orig_name
    | Map.Found _ => new_name reserved $ next orig_name
  }.
Next Obligation.
  clear new_name. destruct v. unfold Map.fold. repeat rewrite MapCore.fold_spec. apply MapCore.bindings_spec1 in Y.
  remember (MapCore.bindings reserved) as b eqn:Eb; clear reserved Eb. generalize dependent orig_name.
  induction b as [| [k v] tail IH]; intros; cbn in *. { invert Y. } repeat rewrite (pull_out_of_acc $ _ _).
  invert Y. { clear IH. destruct H0. cbn in *. subst. rewrite prefix_prime. rewrite prefix_refl. cbn. apply le_prime. }
  specialize (IH _ H0). destruct (prefix (orig_name ++ "'") k) eqn:Ep'. {
    apply prefix_acc in Ep' as ->. apply -> PeanoNat.Nat.succ_lt_mono. exact IH. }
  destruct (prefix orig_name k) eqn:Ep; cbn in *. 2: { exact IH. }
  eapply PeanoNat.Nat.lt_trans. { exact IH. } apply PeanoNat.Nat.lt_succ_diag_r. Qed.
Fail Next Obligation.

Lemma not_in_new_name {reserved orig_name}
  (I : Map.In reserved $ new_name reserved orig_name)
  : False.
Proof.
  funelim (new_name reserved orig_name); cbn in *.
  - rewrite Heqcall in *. apply H in I as [].
  - rewrite <- Heqcall in *. destruct I as [[] F]. apply N in F as [].
Qed.

Lemma unfold_new_name reserved orig_name
  : new_name reserved orig_name = if Map.in_ reserved orig_name then new_name reserved $ next orig_name else orig_name.
Proof.
  unfold Map.in_. funelim (new_name reserved orig_name); cbn in *.
  - repeat rewrite Heqcall in *. assert (tmp := Y). apply Map.find_iff in tmp as ->. reflexivity.
  - destruct (Map.find_spec reserved orig_name). { apply N in Y as []. } reflexivity.
Qed.

(* Yes, exactly equal, not just equivalent: *)
Lemma new_name_det {r1 r2} (E : Map.Eq r1 r2) orig_name
  : new_name r1 orig_name = new_name r2 orig_name.
Proof.
  generalize dependent r2. funelim (new_name r1 orig_name); intros; cbn in *. 2: {
    rewrite unfold_new_name. destruct (Map.in_spec r2 orig_name). 2: { reflexivity. }
    destruct Y as [[] F]. apply E in F. apply N in F as []. }
  specialize (H _ E). rewrite (unfold_new_name r2). assert (F := Y). apply E in F.
  unfold Map.in_. apply Map.find_iff in F as ->. apply H.
Qed.

Lemma new_name_id {reserved name} (N : ~Map.In reserved name)
  : new_name reserved name = name.
Proof. rewrite unfold_new_name. destruct (Map.in_spec reserved name). 2: { reflexivity. } apply N in Y as []. Qed.



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

Lemma in_right {reserved : Map.set} {acc : Map.to string} {tail : list (string * unit)} {k : string} {v : string}
  (F : Map.Find (List.fold_right (fun kv (x : Map.to string) =>
    Map.overriding_add (fst kv) (new_name (Map.overriding_union reserved
      (Map.fold (fun (_ v : string) (acc' : Map.set) => Map.overriding_add v tt acc') Map.empty x))
      (fst kv)) x) acc tail) k v)
  : Map.Find acc k v \/ SetoidList.InA MapCore.eq_key (k, tt) tail.
Proof.
  generalize dependent v. generalize dependent k. generalize dependent acc. generalize dependent reserved.
  induction tail as [| [x y] tail IH]; intros; cbn in *. { left. exact F. }
  apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]. { right. left. reflexivity. }
  edestruct IH as [IH' | IH']; clear IH; [| left | right]. { exact F. } { exact IH'. } right. exact IH'.
Qed.

Lemma in_range_generate_acc {acc} (O2O : Map.OneToOne acc) {x y} (F : Map.Find acc x y) {names} (N : ~Map.In names x) reserved
  : Map.InRange (generate_acc acc reserved names) y.
Proof.
  unfold generate_acc. unfold Map.fold. rewrite MapCore.fold_spec. rewrite <- List.fold_left_rev_right.
  assert (N' : ~SetoidList.InA MapCore.eq_key_elt (x, tt) $ List.rev (MapCore.bindings names)). {
    intro I. apply N. eexists. apply MapCore.bindings_spec1. apply SetoidList.InA_rev. exact I. } clear N. rename N' into N.
  assert (ND := MapCore.bindings_spec2w names). apply SetoidList.NoDupA_rev in ND.
  remember (List.rev (MapCore.bindings names)) as b eqn:Eb; clear names Eb.
  generalize dependent reserved. generalize dependent y. generalize dependent x. generalize dependent acc.
  induction ND as [| [k []] tail N ND IH]; intros; cbn in *. { exists x. exact F. }
  edestruct IH as [x' IH']; clear IH; try eassumption. 3: { exact Map.eq_key_equiv. } { intro I. apply N0. right. exact I. }
  eexists. apply Map.overwrite_if_present_overwrite. right. split. 2: { exact IH'. }
  intros ->. apply in_right in IH' as [IH | IH]. 2: { apply N in IH as []. }
  specialize (O2O _ _ F _ IH) as ->. apply N0. left. split; reflexivity.
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

(*
Lemma in_acc_right {acc k v} (F : Map.Find acc k v) reserved tail
  : Map.Find (List.fold_right (fun (kv : string * unit) (x : Map.to string) => Map.overriding_add (fst kv)
      (new_name (Map.overriding_union reserved (Map.fold (fun (_ v : string) (acc' : Map.to unit) =>
        Map.overriding_add v tt acc') Map.empty x)) (fst kv)) x) acc tail) k v.
Proof.
  generalize dependent reserved. generalize dependent v. generalize dependent k. generalize dependent acc.
  induction tail as [| [kt vt] tail IH]; intros; cbn in *. { exact F. } apply Map.overwrite_if_present_overwrite.
  destruct (String.eqb_spec k kt); [left | right]. 2: { split. { exact n. } eapply IH. exact F. }
  split. { exact e. } subst. TODO.
*)

(* NOTE: we can't claim that `k` maps to itself, since `k` could have been mapped to earlier
 * e.g. `k` is "x'", there's an "x" in the domain, and "x" is reserved, so "x" maps to "x'" and "x'" maps to "x''"
 * ...but we can claim that it's always in the range, no matter what its corresponding key may be *)
Lemma range_generate_acc {reserved x} (N : ~Map.In reserved x) {names} (I : Map.In names x)
  {acc} (O2O : Map.OneToOne acc) (D : Map.Disjoint names acc)
  : Map.InRange (generate_acc acc reserved names) x.
Proof.
  (* INFORMAL PROOF: *)
  (* Note that `new_name` maps anything not in `reserved` to itself.
   * Note further that `generate_acc` just repeatedly calls `new_name` and adds the *result* (not the original key) to `reserved`.
   * So, at some point in `names`, we get to `x` (by assumption `I`).
   * Either before that point, `x` has been mapped to, and then we're done (since anything already mapped will stay mapped),
   * or `x` has not been mapped to, in which case it can't be in `reserved` (since it's not in the original either),
   * and `new_names` will map it to itself, in which case we're also done. *)

  (* See if we're already done: *) destruct (Map.in_range_spec acc x) as [[z F] |]. {
    eapply in_range_generate_acc. { exact O2O. } { exact F. } intro C. eapply D. { exact C. } eexists. exact F. }

  (* To formalize the notion of "at some point in `names`, we get to `x`," induction on the bindings in `names`: *)
  unfold generate_acc. unfold Map.fold. rewrite MapCore.fold_spec. destruct I as [[] F]. apply MapCore.bindings_spec1 in F.
  (* But `fold_left` is a pain in the ass, and it can be trivially converted to `fold_right` by reversing the list: *)
  rewrite <- List.fold_left_rev_right. apply SetoidList.InA_rev in F. assert (ND := MapCore.bindings_spec2w names).
  (* And doing so changes nothing about our assumptions: *)
  apply SetoidList.NoDupA_rev in ND. 2: { exact Map.eq_key_equiv. }
  assert (D' : forall x (Ia : Map.In acc x) (In : SetoidList.InA MapCore.eq_key_elt (x, tt) $ List.rev (MapCore.bindings names)), False). {
    intros z Ia In. eapply D. 2: { exact Ia. } apply -> SetoidList.InA_rev in In.
    apply MapCore.bindings_spec1 in In. exists tt. exact In. } clear D. rename D' into D.
  remember (List.rev (MapCore.bindings names)) as b eqn:Eb; clear names Eb.
  (* OK, actual induction now: *)
  generalize dependent acc. generalize dependent x. generalize dependent reserved.
  induction ND as [| [k []] tail NI ND IH]; intros; cbn in *. { (* Base case is easy: *) invert F. }
  (* Either this is the point in `names` where we encounter `x`, or it's somewhere down the line: *) invert F. 2: {
    (* Inductive case (down the line) should be easy: *)
    edestruct IH as [k' IH']; try eassumption. { intros z Ia In. eapply D. { exact Ia. } right. exact In. }
    clear IH. eexists. apply Map.overwrite_if_present_overwrite. right.
    split. 2: { exact IH'. } intros ->. apply in_right in IH' as [F | F]. 2: { apply NI in F as []. }
    eapply D. { eexists. exact F. } left. split; reflexivity. }
  (* Now the case in which we hit `x`: *)
  clear IH. destruct H0 as [Ek Ev]. cbn in *. subst. clear Ev.
  destruct (Map.in_range_spec (List.fold_right (fun kv s => Map.overriding_add (fst kv) (new_name (Map.overriding_union reserved $
    Map.fold (fun _ v acc => Map.overriding_add v tt acc) Map.empty s) $ fst kv) s) acc tail) k). {
    destruct Y as [j F]. eexists. apply Map.overwrite_if_present_overwrite. right. split. 2: { exact F. }
    intros ->. apply in_right in F as [F | F]. { apply N0. eexists. exact F. } apply NI in F as []. }
  eexists. apply Map.overwrite_if_present_overwrite. left. split. { reflexivity. }
  symmetry. apply new_name_id. intro I. apply Map.in_overriding_union in I as [I | I]. { apply N in I as []. }
  apply Map.in_range in I. apply N1 in I as [].
Qed.

Lemma range_generate {reserved x} (N : ~Map.In reserved x) {names} (I : Map.In names x)
  : Map.InRange (generate reserved names) x.
Proof.
  apply range_generate_acc. { exact N. } { exact I. } { apply Map.one_to_one_empty. }
  intros k In C. apply Map.empty_empty in C as [].
Qed.
