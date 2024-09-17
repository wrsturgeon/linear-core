From LinearCore Require
  MapCore
  .
From LinearCore Require Import
  Invert
  .



Definition to : Type -> Type := MapCore.t.
Arguments to T.

Definition set := to unit.
Arguments set/.



Definition Find {T} (m : to T) k v := MapCore.MapsTo k v m.
Arguments Find {T} m k v.

Definition find {T} (m : to T) k := MapCore.find k m.
Arguments find {T} m k.

Lemma find_spec {T} (m : to T) k
  : Reflect.Option (Find m k) (find m k).
Proof.
  unfold Find. unfold find. destruct MapCore.find as [v |] eqn:F; constructor.
  - apply MapCore.find_spec. exact F.
  - intros v M. apply MapCore.find_spec in M. rewrite M in F. discriminate F.
Qed.

Lemma find_det {T} (m : to T) k v1 (F1 : Find m k v1) v2 (F2 : Find m k v2)
  : v1 = v2.
Proof.
  unfold Find in *. apply MapCore.find_spec in F1. apply MapCore.find_spec in F2.
  rewrite F1 in F2. invert F2. reflexivity.
Qed.

Lemma find_iff {T} (m : to T) k v
  : Find m k v <-> find m k = Some v.
Proof.
  destruct (find_spec m k). { split. { intro F. f_equal. eapply find_det; eassumption. } intro E. invert E. exact Y. }
  split. { intro F. apply N in F as []. } intro D. discriminate D.
Qed.



Definition In {T} (m : to T) k := exists v, Find m k v.
Arguments In {T} m k/.

Definition in_ {T} (m : to T) k := match find m k with Some _ => true | None => false end.
Arguments in_ {T} m k/.

Lemma in_spec {T} (m : to T) k :
  Reflect.Bool (In m k) (in_ m k).
Proof.
  unfold In. unfold in_. destruct (find_spec m k); constructor. { eexists. exact Y. }
  intros [v M]. apply N in M as [].
Qed.



Definition ForAll {T} (P : Name.name -> T -> Prop) (m : to T) : Prop :=
  forall k v (F : Find m k v), P k v.

Definition for_all : forall {T}, (Name.name -> T -> bool) -> to T -> bool := @MapCore.for_all.
Arguments for_all/ {T} p m : rename.

Lemma for_all_spec {T P p} (R : forall k (v : T), Reflect.Bool (P k v) (p k v)) m
  : Reflect.Bool (ForAll P m) (for_all p m).
Proof.
  cbn in *. unfold ForAll. unfold Find. rewrite MapCore.for_all_spec. eapply (Reflect.bool_eq (forall k v
    (F : SetoidList.InA MapCore.eq_key_elt (k, v) (MapCore.bindings m)), P k v)). {
    split; intros H k v; [rewrite MapCore.bindings_spec1 | rewrite <- MapCore.bindings_spec1]; apply H. }
  remember (MapCore.bindings m) as bindings eqn:Eb; clear m Eb.
  induction bindings as [| [k v] tail IH]; cbn in *. { constructor. intros k v C. invert C. }
  destruct (R k v); cbn in *. 2: { constructor. intro C. apply N. apply C. left. split; reflexivity. }
  destruct IH; constructor.
  - intros k' v' I. invert I. 2: { apply Y0. assumption. } invert H0; cbn in *; subst. exact Y.
  - intro C. apply N. intros k' v' I. apply C. right. exact I.
Qed.



Definition maps_to {T} (eqb : T -> T -> bool) m k (v : T) : bool :=
  match find m k with
  | None => false
  | Some v' => eqb v v'
  end.
Arguments maps_to {T} eqb m k v/.

Lemma maps_to_spec {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b)) m k v
  : Reflect.Bool (Find m k v) (maps_to eqb m k v).
Proof.
  unfold maps_to. destruct (find_spec m k). 2: { constructor. apply N. }
  destruct (eqb_spec v x); constructor. { subst. exact Y. } intro C. apply N. eapply find_det; eassumption.
Qed.



Definition Subset {T} (a b : to T) : Prop :=
  forall k v (F : Find a k v), Find b k v.
Arguments Subset {T} a b/.

Definition subset {T} eqb (a b : to T) : bool := for_all (maps_to eqb b) a.
Arguments subset {T} eqb a b/.

Lemma subset_spec {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b)) a b
  : Reflect.Bool (Subset a b) (subset eqb a b).
Proof. apply for_all_spec. apply maps_to_spec. exact eqb_spec. Qed.



Definition Eq {T} (a b : to T) : Prop :=
  forall k v, (Find a k v <-> Find b k v).
Arguments Eq {T} a b/.

Lemma eq_both_subset {T} (a b : to T)
  : Eq a b <-> (Subset a b /\ Subset b a).
Proof. split. { intro E. split; intros k v; apply E. } intro S. split; apply S. Qed.

Definition eq {T} eqb (a b : to T) := andb (subset eqb a b) (subset eqb b a).
Arguments eq {T} eqb a b/.

Lemma eq_spec {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b)) a b
  : Reflect.Bool (Eq a b) (eq eqb a b).
Proof. eapply Reflect.bool_eq. { apply eq_both_subset. } apply Reflect.and; apply subset_spec; exact eqb_spec. Qed.



Definition Empty {T} (m : to T) : Prop :=
  forall k (I : In m k), False.

Definition empty := @MapCore.empty.
Arguments empty/ {T} : rename.

Lemma empty_empty {T} : Empty (@empty T).
Proof. intros k [v F]. invert F. Qed.



Definition Singleton {T} k v (m : to T) : Prop :=
  forall x y, Find m x y <-> (x = k /\ y = v).

Definition singleton : forall {T}, Name.name -> T -> to T := @MapCore.singleton.
Arguments singleton {T} k v.

Lemma find_singleton {T} x y k (v : T)
  : Find (singleton k v) x y <-> (x = k /\ y = v).
Proof.
  split.
  - intro M. apply MapCore.bindings_spec1 in M. rewrite MapCore.singleton_spec in M.
    invert M as [? ? E | ? ? C]. 2: { invert C. } exact E.
  - intros [-> ->]. apply MapCore.bindings_spec1. left. split; reflexivity.
Qed.

Lemma in_singleton {T} x k (v : T)
  : In (singleton k v) x <-> x = k.
Proof.
  split.
  - intros [y M]. apply MapCore.bindings_spec1 in M. rewrite MapCore.singleton_spec in M.
    invert M as [? ? E | ? ? C]. 2: { invert C. } invert E as [Ex Ey]. exact Ex.
  - intros ->. eexists. apply MapCore.bindings_spec1. left. split; reflexivity.
Qed.



Definition AgreeOn {T} k v (m : to T) :=
  forall v' (F : Find m k v'), v' = v.
Arguments AgreeOn {T} k v m/.

Definition agree_on {T} (eqb : T -> T -> bool) k v (m : to T) :=
  match find m k with
  | None => true
  | Some v' => eqb v' v
  end.
Arguments agree_on {T} eqb k v m/.

Lemma agree_on_spec {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b)) k v (m : to T)
  : Reflect.Bool (AgreeOn k v m) (agree_on eqb k v m).
Proof.
  unfold AgreeOn. unfold agree_on. destruct (find_spec m k). 2: { constructor. intros ? F. apply N in F as []. }
  destruct (eqb_spec x v); constructor. { subst. intros. eapply find_det; eassumption. }
  intro C. apply N. apply C. exact Y.
Qed.



Definition Add {T} k v (m m' : to T) : Prop :=
  forall x y, (Find m' x y <-> ((x = k /\ y = v) \/ Find m x y)).
Arguments Add {T} k v m m'/.

(* Cool etymology: <https://www.etymonline.com/word/override>
 * And regarding distinction with "overwrite" (nowhere online has sources, but I think it makes sense):
 * <https://stackoverflow.com/questions/8651562/overwrite-or-override> *)
Definition overriding_add : forall {T}, Name.name -> T -> to T -> to T := @MapCore.add.
Arguments overriding_add {T} k v m.

Definition checked_add {T} (eqb : T -> T -> bool) k v (m : to T) :=
  match find m k with
  | None => Some (overriding_add k v m)
  | Some v' => if eqb v' v then Some m else None
  end.
Arguments checked_add {T} eqb k v m/.

Lemma in_add {T} x k v (m : to T)
  : In (overriding_add k v m) x <-> (x = k \/ In m x).
Proof.
  split.
  - intros [y M]. apply MapCore.find_spec in M. destruct (Name.spec x k); [left | right]. { exact Y. }
    rewrite MapCore.add_spec2 in M. 2: { symmetry. exact N. } eexists. apply MapCore.find_spec. exact M.
  - intros [-> | [y M]]. { eexists. apply MapCore.find_spec. apply MapCore.add_spec1. }
    destruct (Name.spec x k). { subst. eexists. apply MapCore.find_spec. apply MapCore.add_spec1. }
    eexists. apply MapCore.find_spec. rewrite MapCore.add_spec2. 2: { symmetry. exact N. } apply MapCore.find_spec. exact M.
Qed.



(* Crucial for unions: if two maps both map the same key, they both map it to the same value. *)
Definition Agree {T} (a b : to T) : Prop :=
  forall k v (F : Find a k v), AgreeOn k v b.
Arguments Agree {T} a b/.

Definition agree {T} eqb (a : to T) : to T -> bool := for_all (fun k v => agree_on eqb k v a).
Arguments agree {T} eqb a/ b.

Lemma agree_spec {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b)) a b
  : Reflect.Bool (Agree a b) (agree eqb a b).
Proof.
  apply (Reflect.bool_eq (Agree b a)). { cbn. split; intros; specialize (H _ _ F0 _ F) as ->; reflexivity. }
  apply for_all_spec. intros. apply agree_on_spec. exact eqb_spec.
Qed.



Definition Union {T} (a b c : to T) : Prop :=
  forall k v, Find c k v <-> (Find a k v \/ Find b k v).
Arguments Union {T} a b c/.

Lemma union_agree {T} {a b c : to T} (U : Union a b c)
  : Agree a b.
Proof. cbn. intros. eapply find_det; apply U; [right | left]; eassumption. Qed.

Definition override {T} (_ : Name.name) (a b : option T) :=
  match a with Some y => Some y | None => b end.
Arguments override {T} _ a/ b.

Definition overriding_union {T} : to T -> to T -> to T := @MapCore.merge T T T override.
Arguments overriding_union {T} a b : rename.

Definition set_union : set -> set -> set := overriding_union.
Arguments set_union/ a b.

Definition checked_union {T} eqb (a b : to T) := if agree eqb a b then Some (overriding_union a b) else None.
Arguments checked_union {T}/ a b : rename.

Lemma find_overriding_union {T} (a b : to T) x
  : find (overriding_union a b) x = match find a x with Some y => Some y | None => find b x end.
Proof.
  unfold overriding_union. destruct (find_spec a x) as [y M | Na].
  - assert (I : In a x). { eexists. exact M. } unfold find.
    edestruct (@MapCore.merge_spec1 _ _ _ override a b _ (or_introl I)) as [? [-> ->]].
    cbn. apply find_iff in M. unfold find in M. rewrite M. reflexivity.
  - destruct (find_spec b x) as [y M | Nb].
    + assert (I : In b x). { eexists. exact M. } unfold find.
      edestruct (@MapCore.merge_spec1 _ _ _ override a b _ (or_intror I)) as [? [-> ->]].
      cbn. destruct MapCore.find eqn:F. { apply MapCore.find_spec in F. apply Na in F as []. }
      apply MapCore.find_spec. exact M.
    + destruct find eqn:F. 2: { reflexivity. }
      apply MapCore.find_spec in F. assert (I : In (MapCore.merge override a b) x). { eexists. exact F. }
      apply MapCore.merge_spec2 in I as [[y M] | [y M]]; [apply Na in M as [] | apply Nb in M as []].
Qed.

Lemma union_overriding_union {T} (a b : to T) (A : Agree a b)
  : Union a b (overriding_union a b).
Proof.
  split.
  - intro M. apply find_iff in M. rewrite find_overriding_union in M. destruct (find_spec a k).
    + invert M. left. exact Y.
    + apply find_iff in M. right. exact M.
  - intro M. apply find_iff. rewrite find_overriding_union. destruct M as [M | M].
    + apply find_iff in M as ->. reflexivity.
    + destruct (find_spec a k). { f_equal. symmetry. eapply A; eassumption. } apply find_iff. exact M.
Qed.

Lemma find_checked_union {T eqb} {a b c : to T} (E : checked_union eqb a b = Some c) x
  : find c x = match find a x with Some y => Some y | None => find b x end.
Proof. unfold checked_union in E. destruct agree in E; invert E. apply find_overriding_union. Qed.

Lemma union_checked_union {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b))
  {a b c} (E : checked_union eqb a b = Some c)
  : Union a b c.
Proof. unfold checked_union in E. destruct (agree_spec eqb_spec a b); invert E. apply union_overriding_union. exact Y. Qed.

Lemma union_iff {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b)) {a b c : to T}
  : Union a b c <-> exists c', (checked_union eqb a b = Some c' /\ Eq c c').
Proof.
  unfold Union. unfold checked_union. unfold Eq. destruct (agree_spec eqb_spec a b). 2: {
    split. 2: { intros [? [D _]]. discriminate D. } intro U. contradiction N. eapply union_agree. eassumption. }
  eassert (Iff : (exists c', _) <-> forall k v, (Find c k v <-> Find (overriding_union a b) k v)); [| rewrite Iff]. {
    split. { intros [? [tmp E]]; invert tmp. exact E. } intro E. eexists. split. { reflexivity. } exact E. }
  split; intros U' k v; rewrite U'; [symmetry |]; apply union_overriding_union; exact Y.
Qed.
