From LinearCore Require
  MapCore
  .
From LinearCore Require Import
  Invert
  .



Definition to : Type -> Type := MapCore.t.
Arguments to T : simpl never.

Definition set := to unit.
Arguments set/.



Definition Find {T} (m : to T) k v := MapCore.MapsTo k v m.
Arguments Find {T} m k v : simpl never.

Definition find {T} (m : to T) k := MapCore.find k m.
Arguments find {T} m k : simpl never.

Lemma find_spec {T} (m : to T) k
  : Reflect.Option (Find m k) (find m k).
Proof.
  unfold Find. unfold find. destruct MapCore.find as [v |] eqn:F; constructor.
  - apply MapCore.find_spec. exact F.
  - intros v Fx. apply MapCore.find_spec in Fx. rewrite Fx in F. discriminate F.
Qed.

Lemma find_det {T} {m : to T} {k v1} (F1 : Find m k v1) {v2} (F2 : Find m k v2)
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



Definition ForAll {T} (P : Name.name -> T -> Prop) (m : to T) : Prop :=
  forall k v (F : Find m k v), P k v.

Definition for_all : forall T, (Name.name -> T -> bool) -> to T -> bool := @MapCore.for_all.
Arguments for_all {T} p m : rename, simpl never.

Lemma for_all_spec {T P p} (R : forall k (v : T), Reflect.Bool (P k v) (p k v)) m
  : Reflect.Bool (ForAll P m) (for_all p m).
Proof.
  cbn in *. unfold ForAll. unfold Find. rewrite MapCore.for_all_spec. eapply (@Reflect.bool_eq (forall k v
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

Lemma eq_refl {T} (m : to T)
  : Eq m m.
Proof. split; intro F; exact F. Qed.

Lemma eq_sym {T} (a b : to T)
  : Eq a b <-> Eq b a.
Proof. split; intros E k v; cbn in E; rewrite E; reflexivity. Qed.

Lemma eq_trans {T} {a b : to T} (Eab : Eq a b) {c} (Ebc : Eq b c)
  : Eq a c.
Proof. split; intro F; [apply Ebc |]; apply Eab; [| apply Ebc]; exact F. Qed.



Definition In {T} (m : to T) k := exists v, Find m k v.
Arguments In {T} m k/.

Definition in_ {T} (m : to T) k := match find m k with Some _ => true | None => false end.
Arguments in_ {T} m k/.

Lemma in_spec {T} (m : to T) k
  : Reflect.Bool (In m k) (in_ m k).
Proof.
  unfold In. unfold in_. destruct (find_spec m k); constructor. { eexists. exact Y. }
  intros [v F]. apply N in F as [].
Qed.

Lemma in_eq {T} {m1 m2 : to T} (E : Eq m1 m2) x
  : In m1 x <-> In m2 x.
Proof. split; intros [y F]; eexists; apply E; exact F. Qed.



Definition InRange {T} (m : to T) v := exists k, Find m k v.
Arguments InRange {T} m v/.



Definition Empty {T} (m : to T) : Prop :=
  forall k (I : In m k), False.

Definition empty := @MapCore.empty.
Arguments empty {T} : rename, simpl never.

Lemma empty_empty {T} : Empty (@empty T).
Proof. intros k [v F]. invert F. Qed.



Definition Singleton {T} k v (m : to T) : Prop :=
  forall x y, Find m x y <-> (x = k /\ y = v).
Arguments Singleton {T} k v m/.

Definition singleton : forall T, Name.name -> T -> to T := @MapCore.singleton.
Arguments singleton {T} k v : simpl never.

Lemma find_singleton {T} x y k (v : T)
  : Find (singleton k v) x y <-> (x = k /\ y = v).
Proof.
  split.
  - intro F. apply MapCore.bindings_spec1 in F. rewrite MapCore.singleton_spec in F.
    invert F as [? ? E | ? ? C]. 2: { invert C. } exact E.
  - intros [-> ->]. apply MapCore.bindings_spec1. left. split; reflexivity.
Qed.

Lemma in_singleton {T} x k (v : T)
  : In (singleton k v) x <-> x = k.
Proof.
  split.
  - intros [y F]. apply MapCore.bindings_spec1 in F. rewrite MapCore.singleton_spec in F.
    invert F as [? ? E | ? ? C]. 2: { invert C. } invert E as [Ex Ey]. exact Ex.
  - intros ->. eexists. apply MapCore.bindings_spec1. left. split; reflexivity.
Qed.

Lemma singleton_singleton k {T} (v : T)
  : Singleton k v (singleton k v).
Proof. cbn. intros. apply find_singleton. Qed.

Lemma singleton_det k {T} (v : T)
  m1 (S1 : Singleton k v m1)
  m2 (S2 : Singleton k v m2)
  : Eq m1 m2.
Proof. cbn in *. intros. rewrite S1. rewrite S2. reflexivity. Qed.



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
 * And regarding distinction with "overwrite" (nowhere online has sources, but I think it makes sense),
 * <https://stackoverflow.com/questions/8651562/overwrite-or-override> *)
Definition overriding_add : forall T, Name.name -> T -> to T -> to T := @MapCore.add.
Arguments overriding_add {T} k v m : simpl never.

Definition checked_add {T} (eqb : T -> T -> bool) k v (m : to T) :=
  match find m k with
  | None => Some (overriding_add k v m)
  | Some v' => if eqb v' v then Some m else None
  end.
Arguments checked_add {T} eqb k v m/.

Definition disjoint_add {T} k v (m : to T) :=
  match find m k with
  | None => Some (overriding_add k v m)
  | Some v' => None
  end.
Arguments disjoint_add {T} k v m/.

Lemma find_overriding_add {T} {k v} {m : to T} x y
  : Find (overriding_add k v m) x y <-> ((x = k /\ y = v) \/ (x <> k /\ Find m x y)).
Proof.
  split.
  - intro F. apply MapCore.find_spec in F. destruct (Name.spec x k); [left | right].
    + subst. split. { reflexivity. } unfold overriding_add in F.
      rewrite MapCore.add_spec1 in F. { invert F. subst. reflexivity. }
    + rewrite MapCore.add_spec2 in F. 2: { symmetry. exact N. } split. { assumption. } apply MapCore.find_spec. exact F.
  - intros [[-> ->] | [N F]]. { apply MapCore.find_spec. apply MapCore.add_spec1. }
    apply MapCore.find_spec. rewrite MapCore.add_spec2. 2: { symmetry. exact N. } apply MapCore.find_spec. exact F.
Qed.

Lemma in_add {T k v m m'} (A : @Add T k v m m') x
  : In m' x <-> (x = k \/ In m x).
Proof.
  split.
  - intros [y F]. apply A in F as [[-> ->] | F]; [left | right]. { reflexivity. } eexists. exact F.
  - intros [-> | [y F]]; eexists; apply A; [left | right]. { split; reflexivity. } exact F.
Qed.

Lemma in_overriding_add {T} x k v (m : to T)
  : In (overriding_add k v m) x <-> (x = k \/ In m x).
Proof.
  split.
  - intros [y F]. apply MapCore.find_spec in F. destruct (Name.spec x k); [left | right]. { exact Y. }
    rewrite MapCore.add_spec2 in F. 2: { symmetry. exact N. } eexists. apply MapCore.find_spec. exact F.
  - intros [-> | [y F]]. { eexists. apply MapCore.find_spec. apply MapCore.add_spec1. }
    destruct (Name.spec x k). { subst. eexists. apply MapCore.find_spec. apply MapCore.add_spec1. }
    eexists. apply MapCore.find_spec. rewrite MapCore.add_spec2. 2: { symmetry. exact N. }
    apply MapCore.find_spec. exact F.
Qed.

Lemma add_overriding {T} {k v} {m : to T} (A : AgreeOn k v m)
  : Add k v m (overriding_add k v m).
Proof.
  cbn. intros. rewrite find_overriding_add. split; (intros [[-> ->] | F]; [left; split; reflexivity |]).
  - destruct F as [N F]. right. exact F.
  - destruct (Name.spec x k). { subst. left. split. { reflexivity. } apply A. exact F. }
    right. split. { exact N. } exact F.
Qed.

Lemma find_checked_add {T eqb} (eqb_spec : forall a b, Reflect.Bool (a = b) (eqb a b))
  {k v} {m m' : to T} (E : checked_add eqb k v m = Some m') x y
  : Find m' x y <-> ((x = k /\ y = v) \/ Find m x y).
Proof.
  unfold checked_add in E. destruct (find_spec m k) as [v' F | N].
  - destruct (eqb_spec v' v); invert E. split. { intro F'. right. exact F'. }
    intros [[-> ->] | F']. { exact F. } exact F'.
  - invert E. rewrite find_overriding_add. split; (intros [[-> ->] | F]; [left; split; reflexivity |]).
    + destruct F as [N' F]. right. exact F.
    + right. split. { intros ->. apply N in F as []. } assumption.
Qed.

Lemma in_checked_add {T eqb} (eqb_spec : forall a b, Reflect.Bool (a = b) (eqb a b))
  {k v} {m m' : to T} (E : checked_add eqb k v m = Some m') x
  : In m' x <-> (x = k \/ In m x).
Proof.
  unfold checked_add in E. destruct (find_spec m k) as [v' F | N].
  - destruct (eqb_spec v' v); invert E. split. { intro F'. right. exact F'. }
    intros [-> | F']. { eexists. exact F. } exact F'.
  - invert E. apply in_overriding_add.
Qed.

Lemma add_checked {T eqb} (eqb_spec : forall a b, Reflect.Bool (a = b) (eqb a b))
  {k v} {m m' : to T} (E : checked_add eqb k v m = Some m')
  : Add k v m m'.
Proof.
  unfold checked_add in E. destruct (find_spec m k) as [v' F | N].
  - destruct (eqb_spec v' v); invert E. split. { intro F'. right. exact F'. }
    intros [[-> ->] | F']. { exact F. } exact F'.
  - invert E. apply add_overriding. cbn. intros. apply N in F as [].
Qed.

Lemma find_disjoint_add {T k v} {m m' : to T} (E : disjoint_add k v m = Some m') x y
  : Find m' x y <-> ((x = k /\ y = v) \/ Find m x y).
Proof.
  unfold disjoint_add in E. destruct (find_spec m k) as [v' F | N]. { discriminate E. }
  invert E. rewrite find_overriding_add. split; (intros [[-> ->] | F]; [left; split; reflexivity |]).
  - destruct F as [N' F]. right. exact F.
  - right. split. 2: { exact F. } intros ->. apply N in F as [].
Qed.

Lemma in_disjoint_add {T k v} {m m' : to T} (E : disjoint_add k v m = Some m') x
  : In m' x <-> (x = k \/ In m x).
Proof.
  unfold disjoint_add in E. destruct (find_spec m k) as [v' F | N]. { discriminate E. }
  invert E. apply in_overriding_add.
Qed.

Lemma add_disjoint {T k v} {m m' : to T} (E : disjoint_add k v m = Some m')
  : Add k v m m'.
Proof.
  unfold disjoint_add in E. destruct (find_spec m k) as [v' F | N].
  invert E. invert E. apply add_overriding. cbn. intros. apply N in F as [].
Qed.

Lemma add_det
  k1 {T} (v1 : T) m1 m1' (A1 : Add k1 v1 m1 m1')
  k2 (Ek : k1 = k2)
  v2 (Ev : v1 = v2)
  m2 (Em : Eq m1 m2)
  m2' (A2 : Add k2 v2 m2 m2')
  : Eq m1' m2'.
Proof. cbn in *. intros x y. subst. rewrite A1. rewrite A2. rewrite Em. reflexivity. Qed.

Lemma add_eq
  k1 {T} (v1 : T) m1 m1' (A1 : Add k1 v1 m1 m1')
  k2 (Ek : k1 = k2)
  v2 (Ev : v1 = v2)
  m2 (Em : Eq m1 m2)
  m2' (Em' : Eq m1' m2')
  : Add k2 v2 m2 m2'.
Proof.
  subst. split.
  - intro F. apply Em' in F. apply A1 in F as [[-> ->] | F]; [left | right]. { split; reflexivity. } apply Em. exact F.
  - intro F. apply Em'. apply A1. destruct F as [[-> ->] | F]; [left | right]. { split; reflexivity. } apply Em. exact F.
Qed.



Definition OverwriteIfPresent {T} k v (m m' : to T) : Prop :=
  forall x y, (Find m' x y <-> ((x = k /\ y = v) \/ (x <> k /\ Find m x y))).
Arguments OverwriteIfPresent {T} k v m m'/.

Definition overwrite := @overriding_add.
Arguments overwrite {T} k v m/.

Lemma overwrite_if_present_overwrite {T} k m (v : T)
  : OverwriteIfPresent k v m (overwrite k v m).
Proof. cbn. intros. apply find_overriding_add. Qed.

Lemma overwrite_if_present_det {T}
  k1 (v1 : T) m1 m1' (O1 : OverwriteIfPresent k1 v1 m1 m1')
  k2 (Ek : k1 = k2)
  v2 (Ev : v1 = v2)
  m2 (Em : Eq m1 m2)
  m2' (O2 : OverwriteIfPresent k2 v2 m2 m2')
  : Eq m1' m2'.
Proof. cbn in *. intros x y. subst. rewrite O1. rewrite O2. cbn in Em. rewrite Em. reflexivity. Qed.

Lemma overwrite_if_present_eq {T}
  k1 (v1 : T) m1 m1' (O1 : OverwriteIfPresent k1 v1 m1 m1')
  k2 (Ek : k1 = k2)
  v2 (Ev : v1 = v2)
  m2 (Em : Eq m1 m2)
  m2' (Em' : Eq m1' m2')
  : OverwriteIfPresent k2 v1 m2 m2'.
Proof. cbn in *. subst. intros. cbn in Em'. rewrite <- Em'. rewrite O1. cbn in Em. rewrite Em. reflexivity. Qed.

Lemma in_overwrite_if_present {T k v m m'} (O : @OverwriteIfPresent T k v m m') x
  : In m' x <-> (x = k \/ In m x).
Proof.
  split.
  - intros [y F]. apply O in F as [[-> ->] | [N F]]; [left | right]. { reflexivity. } eexists. exact F.
  - intros [-> | [y F]]. { eexists. apply O. left. split; reflexivity. }
    destruct (Name.spec x k); subst; eexists; apply O; [left | right]. { split; reflexivity. } split; eassumption.
Qed.



Definition Overwrite {T} k v (m m' : to T) : Prop :=
  In m k /\ (* <-- this proof should be easy wherever `Overwrite` is used, but it's a sanity check *)
  OverwriteIfPresent k v m m'.
Arguments Overwrite {T} k v m m'/.

Lemma overwrite_overwrite {T} k m (I : In m k) (v : T)
  : Overwrite k v m (overwrite k v m).
Proof. split. { exact I. } apply overwrite_if_present_overwrite. Qed.

Lemma overwrite_det {T}
  k1 (v1 : T) m1 m1' (O1 : Overwrite k1 v1 m1 m1')
  k2 (Ek : k1 = k2)
  v2 (Ev : v1 = v2)
  m2 (Em : Eq m1 m2)
  m2' (O2 : Overwrite k2 v2 m2 m2')
  : Eq m1' m2'.
Proof. destruct O1 as [I1 O1]. destruct O2 as [I2 O2]. eapply overwrite_if_present_det; eassumption. Qed.

Lemma overwrite_eq {T}
  k1 (v1 : T) m1 m1' (O : Overwrite k1 v1 m1 m1')
  k2 (Ek : k1 = k2)
  v2 (Ev : v1 = v2)
  m2 (Em : Eq m1 m2)
  m2' (Em' : Eq m1' m2')
  : Overwrite k2 v1 m2 m2'.
Proof.
  subst. destruct O as [I O]. split. 2: { eapply overwrite_if_present_eq; try reflexivity; eassumption. }
  eapply in_eq. { apply eq_sym. exact Em. } exact I.
Qed.

Lemma in_overwrite {T k v m m'} (O : @Overwrite T k v m m') x
  : In m' x <-> In m x.
Proof.
  destruct O as [I O].
  split; intros [y F]. { apply O in F as [[-> ->] | [N F]]. { exact I. } eexists. exact F. }
  destruct (Name.spec x k). { eexists. apply O. left. split. { exact Y. } reflexivity. }
  eexists. apply O. right. split. { exact N. } exact F.
Qed.



Definition RemoveIfPresent {T} k (m m' : to T) : Prop :=
  forall x y, (Find m' x y <-> (x <> k /\ Find m x y)).
Arguments RemoveIfPresent {T} k m m'/.

Definition remove := @MapCore.remove.
Arguments remove {T} k m : rename, simpl never.

Lemma remove_if_present_remove {T} k (m : to T)
  : RemoveIfPresent k m (remove k m).
Proof.
  cbn. intros. rewrite find_iff. unfold find. unfold remove. destruct (Name.spec k x).
  - subst. rewrite MapCore.remove_spec1. split. { intro D. discriminate D. } intros [C _]. contradiction C. reflexivity.
  - rewrite MapCore.remove_spec2. 2: { exact N. } fold (find m x). rewrite <- find_iff.
    split. { intro F. split. { symmetry. exact N. } exact F. } intros [_ F]. exact F.
Qed.

Lemma remove_if_present_det {T k1} {m1 m1' : to T} (R1 : RemoveIfPresent k1 m1 m1')
  {k2} (Ek : k1 = k2)
  {m2} (Em : Map.Eq m1 m2)
  {m2'} (R2 : RemoveIfPresent k2 m2 m2')
  : Map.Eq m1' m2'.
Proof. subst. cbn in *. intros x y. rewrite R1. rewrite R2. cbn in Em. rewrite Em. reflexivity. Qed.

Lemma in_remove_if_present {T k} {m m' : to T} (R : RemoveIfPresent k m m') x
  : In m' x <-> (x <> k /\ In m x).
Proof.
  split.
  - intros [y F]. apply R in F as [N F]. split. { exact N. } eexists. exact F.
  - intros [N [y F]]. eexists. apply R. split. { exact N. } exact F.
Qed.

Lemma find_remove_if_present {T k} {m m' : to T} (R : RemoveIfPresent k m m') x y
  : Find m' x y <-> (x <> k /\ Find m x y).
Proof.
  split.
  - intro F. apply R in F as [N F]. split. { exact N. } exact F.
  - intros [N F]. apply R. split. { exact N. } exact F.
Qed.



Definition Remove {T} k (m m' : to T) : Prop :=
  In m k /\ RemoveIfPresent k m m'.
Arguments Remove {T} k m m'/.

Lemma remove_remove {T k} {m : to T} (I : In m k)
  : Remove k m (remove k m).
Proof. split. { exact I. } apply remove_if_present_remove. Qed.

Lemma remove_det {T k1} {m1 m1' : to T} (R1 : Remove k1 m1 m1')
  {k2} (Ek : k1 = k2)
  {m2} (Em : Map.Eq m1 m2)
  {m2'} (R2 : Remove k2 m2 m2')
  : Map.Eq m1' m2'.
Proof. eapply remove_if_present_det. { apply R1. } { exact Ek. } { exact Em. } apply R2. Qed.

Lemma in_remove {T k} {m m' : to T} (R : Remove k m m') x
  : In m' x <-> (x <> k /\ In m x).
Proof. apply in_remove_if_present. apply R. Qed.



(* Crucial for unions: if two maps both map the same key, they both map it to the same value. *)
Definition Agree {T} (a b : to T) : Prop :=
  forall k v (F : Find a k v), AgreeOn k v b.
Arguments Agree {T} a b/.

Definition agree {T} eqb (a : to T) : to T -> bool := for_all (fun k v => agree_on eqb k v a).
Arguments agree {T} eqb a/ b.

Lemma agree_spec {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b)) a b
  : Reflect.Bool (Agree a b) (agree eqb a b).
Proof.
  apply (@Reflect.bool_eq (Agree b a)). { cbn. split; intros; specialize (H _ _ F0 _ F) as ->; reflexivity. }
  apply for_all_spec. intros. apply agree_on_spec. exact eqb_spec.
Qed.



Definition Union {T} (a b c : to T) : Prop :=
  forall k v, Find c k v <-> (Find a k v \/ Find b k v).
Arguments Union {T} a b c/.

Lemma union_agree {T} {a b c : to T} (U : Union a b c)
  : Agree a b.
Proof. cbn. intros. eapply find_det; apply U; [right | left]; eassumption. Qed.

Definition override {T} {_ : Name.name} (a b : option T) :=
  match a with Some y => Some y | None => b end.
Arguments override {T _} a/ b.

Definition overriding_union {T} : to T -> to T -> to T := @MapCore.merge T T T (@override _).
Arguments overriding_union {T} a b : rename, simpl never.

Definition set_union : set -> set -> set := overriding_union.
Arguments set_union/ a b.

Definition checked_union {T} eqb (a b : to T) := if agree eqb a b then Some (overriding_union a b) else None.
Arguments checked_union {T}/ a b : rename.

Lemma find_overriding_union {T} (a b : to T) x
  : find (overriding_union a b) x = match find a x with Some y => Some y | None => find b x end.
Proof.
  unfold overriding_union. destruct (find_spec a x) as [y F | Na].
  - assert (I : In a x). { eexists. exact F. } unfold find.
    edestruct (@MapCore.merge_spec1 _ _ _ (@override _) a b _ (or_introl I)) as [? [-> ->]].
    cbn. apply find_iff in F. unfold find in F. rewrite F. reflexivity.
  - destruct (find_spec b x) as [y F | Nb].
    + assert (I : In b x). { eexists. exact F. } unfold find.
      edestruct (@MapCore.merge_spec1 _ _ _ (@override _) a b _ (or_intror I)) as [? [-> ->]].
      cbn. destruct MapCore.find eqn:Ef. { apply MapCore.find_spec in Ef. apply Na in Ef as []. }
      apply MapCore.find_spec. exact F.
    + destruct find eqn:F. 2: { reflexivity. }
      apply MapCore.find_spec in F. assert (I : In (MapCore.merge (@override T) a b) x). { eexists. exact F. }
      apply MapCore.merge_spec2 in I as [[y F'] | [y F']]; [apply Na in F' as [] | apply Nb in F' as []].
Qed.

Lemma in_overriding_union {T} (a b : to T) x
  : In (overriding_union a b) x <-> In a x \/ In b x.
Proof.
  split.
  - intros [y F]. apply find_iff in F. rewrite find_overriding_union in F.
    destruct (find_spec a x). { invert F. left. eexists. exact Y. } right. eexists. apply find_iff. exact F.
  - intros [[y F] | [y F]].
    + eexists; apply find_iff; rewrite find_overriding_union. apply find_iff in F. rewrite F. reflexivity.
    + destruct (find_spec a x); eexists; apply find_iff; rewrite find_overriding_union.
      * apply find_iff in Y. rewrite Y. reflexivity.
      * destruct (find_spec a x). { apply N in Y as []. } apply find_iff. exact F.
Qed.

Lemma union_overriding {T} {a b : to T} (A : Agree a b)
  : Union a b (overriding_union a b).
Proof.
  split.
  - intro F. apply find_iff in F. rewrite find_overriding_union in F. destruct (find_spec a k).
    + invert F. left. exact Y.
    + apply find_iff in F. right. exact F.
  - intro F. apply find_iff. rewrite find_overriding_union. destruct F as [F | F].
    + apply find_iff in F as ->. reflexivity.
    + destruct (find_spec a k). { f_equal. symmetry. eapply A; eassumption. } apply find_iff. exact F.
Qed.

Lemma find_checked_union {T eqb} {a b c : to T} (E : checked_union eqb a b = Some c) x
  : find c x = match find a x with Some y => Some y | None => find b x end.
Proof. unfold checked_union in E. destruct agree in E; invert E. apply find_overriding_union. Qed.

Lemma union_checked {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b))
  {a b c} (E : checked_union eqb a b = Some c)
  : Union a b c.
Proof. unfold checked_union in E. destruct (agree_spec eqb_spec a b); invert E. apply union_overriding. exact Y. Qed.

Lemma union_iff {T eqb} (eqb_spec : forall a b : T, Reflect.Bool (a = b) (eqb a b)) (a b c : to T)
  : Union a b c <-> exists c', (checked_union eqb a b = Some c' /\ Eq c c').
Proof.
  unfold Union. unfold checked_union. unfold Eq. destruct (agree_spec eqb_spec a b). 2: {
    split. 2: { intros [? [D _]]. discriminate D. } intro U. contradiction N. eapply union_agree. eassumption. }
  eassert (Iff : (exists c', _) <-> forall k v, (Find c k v <-> Find (overriding_union a b) k v)); [| rewrite Iff]. {
    split. { intros [? [tmp E]]; invert tmp. exact E. } intro E. eexists. split. { reflexivity. } exact E. }
  split; intros U' k v; rewrite U'; [symmetry |]; apply union_overriding; exact Y.
Qed.

Lemma union_det {T}
  {a1 b1 c1} (U1 : @Union T a1 b1 c1)
  {a2} (Ea : Eq a1 a2)
  {b2} (Eb : Eq b1 b2)
  {c2} (U2 : Union a2 b2 c2)
  : Eq c1 c2.
Proof. cbn in *. intros x y. rewrite U1. rewrite U2. rewrite Ea. rewrite Eb. reflexivity. Qed.



Definition Reflect (P : Name.name -> Prop) (p : set) : Prop :=
  forall x, (In p x <-> P x).
Arguments Reflect P p/.



(*
Definition Map {X Y} (f : Name.name -> X -> Y) m m' : Prop :=
  forall k, (
    (forall v (F : Find m k v), Find m' k (f k v)) /\
    (forall (N : ~In m k) (I : In m' k), False)
  ).
Arguments Map {X Y} f m m'/.
*)

Definition map : forall X Y, (Name.name -> X -> Y) -> Map.to X -> Map.to Y := @MapCore.mapi.
Arguments map {X Y} f m : simpl never.



Definition domain {T} : to T -> set := map (fun k v => tt).
Arguments domain {T} m/.

Lemma find_domain {T} k v (m : to T)
  : Find (domain m) k v <-> In m k.
Proof.
  destruct v. assert (Iff : In m k <-> exists v, SetoidList.InA MapCore.eq_key_elt (k, v) (MapCore.bindings m)). {
    split; intros [v' F]; exists v'; apply MapCore.bindings_spec1; exact F. }
  rewrite Iff; clear Iff. unfold Find. rewrite <- MapCore.bindings_spec1. unfold domain. unfold map.
  rewrite MapCore.mapi_spec. remember (MapCore.bindings m) as b eqn:Eb; clear m Eb; rename b into m.
  generalize dependent k. induction m as [| [x y] tail IH]; intros; cbn in *. {
    split; [intro I | intros [v' I]]; invert I. } split; [intro I | intros [v' I]].
  - invert I. { destruct H0; cbn in *; subst. eexists. left. split; reflexivity. }
    apply IH in H0 as [v' I]. eexists. right. exact I.
  - invert I. { destruct H0; cbn in *; subst. left. split; reflexivity. }
    right. apply IH. eexists. exact H0.
Qed.



Definition fold {X Y} (f : Name.name -> X -> Y -> Y) (acc : Y) (m : to X) : Y := @MapCore.fold X Y f m acc.
Arguments fold {X Y} f acc m : simpl never.



Definition Minus {T} (everything : to T) (discard : set) (subtracted : to T) : Prop :=
  forall k v, Find subtracted k v <-> (Find everything k v /\ forall (discarded : In discard k), False).
Arguments Minus {T} everything discard subtracted/.

Definition minus {T} : to T -> set -> to T := fold (fun k _ acc => remove k acc).
Arguments minus {T} everything discard/.

Lemma minus_minus {T} (everything : to T) discard
  : Minus everything discard (minus everything discard).
Proof.
  cbn. intros. unfold fold. rewrite MapCore.fold_spec. assert (Iff :
    (Find everything k v /\ (forall (discarded : exists v, Find discard k v), False)) <->
    (Find everything k v /\ (forall (discarded : exists v,
      SetoidList.InA MapCore.eq_key_elt (k, v) (MapCore.bindings discard)), False))). {
    split; intros [F N]; (split; [exact F |]); intros [v' N'];
    apply N; exists v'; apply MapCore.bindings_spec1; exact N'. } rewrite Iff; clear Iff.
  remember (MapCore.bindings discard) as b eqn:Eb; clear discard Eb; rename b into discard.
  generalize dependent k. generalize dependent T. induction discard as [| [k v] tail IH]; intros; cbn in *. {
    split. { intro F. split. { exact F. } intros [v' I]. invert I. } intros [F N]. exact F. }
  rewrite IH; clear IH. split; intros [F N].
  - eapply find_remove_if_present in F as [Nk F]. 2: { apply remove_if_present_remove. }
    split. { exact F. } intros [v' C]. apply N. invert C. 2: { eexists. eassumption. }
    destruct H0; cbn in *; subst. contradiction Nk. reflexivity.
  - split. 2: { intros [v' C]. apply N. eexists. right. exact C. }
    eapply find_remove_if_present. { apply remove_if_present_remove. } split. 2: { exact F. }
    intros ->. apply N. eexists. left. split; reflexivity.
Qed.



Definition BulkOverwrite {T} (force original overwritten : to T) : Prop :=
  forall x y, (Find overwritten x y <-> (Find force x y \/ ((forall (I : In force x), False) /\ Find original x y))).
Arguments BulkOverwrite {T} force original overwritten/.

Definition bulk_overwrite := @overriding_union.
Arguments bulk_overwrite {T} a b/.

Lemma bulk_overwrite_bulk_overwrite {T} (force original : to T)
  : BulkOverwrite force original (bulk_overwrite force original).
Proof.
  intros x y. rewrite find_iff. rewrite find_overriding_union. split.
  - intro E. destruct (find_spec force x); [left | right]. { invert E. exact Y. }
    split. 2: { apply find_iff. exact E. } intros [f F]. apply N in F as [].
  - intros [F | [N F]]. { apply find_iff in F. rewrite F. reflexivity. }
    destruct (find_spec force x). { edestruct N. eexists. exact Y. } apply find_iff. exact F.
Qed.

Lemma bulk_overwrite_det {T}
  {f1 o1 y1 : to T} (O1 : BulkOverwrite f1 o1 y1)
  {f2} (Ef : Eq f1 f2)
  {o2} (Eo : Eq o1 o2)
  {y2} (O2 : BulkOverwrite f2 o2 y2)
  : Eq y1 y2.
Proof.
  cbn in *. intros. rewrite O1. rewrite O2. assert (A := in_eq Ef).
  cbn in A. rewrite A. rewrite Ef. rewrite Eo. reflexivity.
Qed.

Lemma bulk_overwrite_eq {T}
  {f1 o1 y1 : to T} (O1 : BulkOverwrite f1 o1 y1)
  {f2} (Ef : Eq f1 f2)
  {o2} (Eo : Eq o1 o2)
  {y2} (Ey : Eq y1 y2)
  : BulkOverwrite f2 o2 y2.
Proof.
  cbn in *. intros. rewrite <- Ey. rewrite O1. assert (A := in_eq Ef).
  cbn in A. rewrite A. rewrite Ef. rewrite Eo. reflexivity.
Qed.

Lemma in_bulk_overwrite {T force original overwritten} (O : @BulkOverwrite T force original overwritten) x
  : In overwritten x <-> (In force x \/ ((forall (I : In force x), False) /\ In original x)).
Proof.
  split.
  - intros [y F]. apply O in F as [F | [N F]]; [left | right]. { eexists. exact F. }
    split. { exact N. } eexists. exact F.
  - intros [[y F] | [N [y F]]]; eexists; apply O; [left | right]. { exact F. } split. { exact N. } exact F.
Qed.



Definition ToSelf (domain : set) to_self : Prop :=
  forall x y, Find to_self x y <-> (In domain x /\ x = y).
Arguments ToSelf domain to_self/.

Definition to_self : set -> to Name.name := map (fun k _ => k).
Arguments to_self domain/.

Lemma to_self_to_self domain
  : ToSelf domain (to_self domain).
Proof.
  cbn in *. intros x y. unfold Find at 1. rewrite <- MapCore.bindings_spec1. unfold map. rewrite MapCore.mapi_spec.
  fold (In domain x). assert (Iff : In domain x <-> exists y,
    SetoidList.InA MapCore.eq_key_elt (x, y) (MapCore.bindings domain)). {
    split; intros [y' F]; exists y'; apply MapCore.bindings_spec1; exact F. }
  rewrite Iff; clear Iff. remember (MapCore.bindings domain) as b eqn:Eb; clear domain Eb. rename b into domain.
  generalize dependent y. generalize dependent x. induction domain as [| [k v] tail IH]; intros; cbn in *. {
    split. { intro I. invert I. } intros [[y' I] E]. invert I. } split.
  - intro I. invert I. { destruct H0; cbn in *; subst. split. { eexists. left. split; reflexivity. } reflexivity. }
    apply IH in H0 as [[y' I] ->]. split. 2: { reflexivity. } eexists. right. exact I.
  - intros [[y' I] ->]. invert I. { destruct H0; cbn in *; subst. left. split; reflexivity. }
    right. apply IH. split. 2: { reflexivity. } eexists. eassumption.
Qed.

Lemma in_to_self domain x
  : In (to_self domain) x <-> In domain x.
Proof.
  split; intros [y F]. { apply to_self_to_self in F as [I ->]. exact I. }
  eexists. apply to_self_to_self. split. { eexists. exact F. } reflexivity.
Qed.

Lemma to_self_det {d1 y1} (TS1 : ToSelf d1 y1)
  {d2} (Ed : Map.Eq d1 d2)
  {y2} (TS2 : ToSelf d2 y2)
  : Eq y1 y2.
Proof.
  split; intro F; [apply TS1 in F | apply TS2 in F]; destruct F as [I E]; [apply TS2 | apply TS1];
  (split; [| exact E]); (eapply in_eq; [| exact I]); try assumption; apply eq_sym; assumption.
Qed.



Lemma sorted_lt {T}
  {kv : _ * T} {tail} (S : Sorted.Sorted MapCore.lt_key tail) (L : Sorted.HdRel MapCore.lt_key kv tail)
  (N : ~SetoidList.InA MapCore.eq_key kv tail) (ND : SetoidList.NoDupA MapCore.eq_key tail)
  {xy} (I : SetoidList.InA MapCore.eq_key_elt xy tail)
  : MapCore.lt_key kv xy.
Proof.
  generalize dependent xy. generalize dependent ND. generalize dependent kv.
  induction S; intros; invert I; destruct xy as [x y]; destruct kv as [k v]; destruct a as [k' v'].
  - destruct H1; cbn in *; subst. invert L. assumption.
  - invert L. invert ND.  apply IHS; try assumption. 2: { intro I. apply N. right. exact I. }
    destruct l. { invert H1. } constructor. eapply Name.trans. { eassumption. } invert H. assumption.
Qed.

Lemma bindings_eq {T} a b
  : @Eq T a b <-> MapCore.bindings a = MapCore.bindings b.
Proof.
  split; intro E.
  - assert (Sa := MapCore.bindings_spec2 a). assert (Sb := MapCore.bindings_spec2 b).
    assert (NDa := MapCore.bindings_spec2w a). assert (NDb := MapCore.bindings_spec2w b).
    assert (Iff : Eq a b <-> forall x y, (
      SetoidList.InA MapCore.eq_key_elt (x, y) (MapCore.bindings a) <->
      SetoidList.InA MapCore.eq_key_elt (x, y) (MapCore.bindings b))). {
      split; intros E' x y; specialize (E' x y); [repeat rewrite MapCore.bindings_spec1 |
        repeat rewrite MapCore.bindings_spec1 in E']; exact E'. }
    rewrite Iff in E; clear Iff.
    remember (MapCore.bindings a) as ba eqn:Ea; clear a Ea; rename ba into a.
    remember (MapCore.bindings b) as bb eqn:Eb; clear b Eb; rename bb into b.
    generalize dependent b. generalize dependent NDa.
    induction Sa as [| [ka va] a' Sa' IH La]; intros; cbn in *. {
      destruct b as [| [k v] tail]. { reflexivity. } assert (A : SetoidList.InA MapCore.eq_key_elt
        (k, v) ((k, v) :: tail)). { left. split; reflexivity. } apply E in A. invert A. }
    invert NDa as [| ? ? Na NDa']. invert NDb as [| shit b' Nb NDb']. {
      assert (A : SetoidList.InA MapCore.eq_key_elt (ka, va) ((ka, va) :: a')). { left. split; reflexivity. }
      apply E in A. invert A. }
    invert Sb as [| [kb vb] b Sb' Lb]. destruct (Name.compare_spec ka kb).
    + cbn in H. subst. f_equal.
      * f_equal. specialize (E kb vb).
        assert (A : SetoidList.InA MapCore.eq_key_elt (kb, vb) ((kb, vb) :: b')). { left. split; reflexivity. }
        apply E in A. invert A. { destruct H0; cbn in *; subst. reflexivity. }
        contradiction Na. clear Sa' La IH b' E Nb NDb' Sb' Lb Na NDa'.
        induction a'; invert H0; [left | right]. { apply H1. } apply IHa'. assumption.
      * apply IH; try assumption. split; intro I; (eassert (I' : SetoidList.InA _ _ _); [right; exact I |]);
        apply E in I'; (invert I'; [| assumption]); destruct H0; cbn in *; subst; [contradiction Na | contradiction Nb];
        cbn; clear Sa' La IH Na E NDa' Nb NDb' Sb' Lb; (induction I; [left; apply H | right; exact IHI]).
    + assert (A : SetoidList.InA MapCore.eq_key_elt (ka, va) ((kb, vb) :: b')). { apply E. left. split; reflexivity. }
      invert A as [| ? ? I]. { destruct H0; cbn in *; subst. rewrite Name.compare_refl in H. discriminate H. }
      assert (L : MapCore.lt_key (kb, vb) (ka, va)). { eapply sorted_lt; try exact I; eassumption. }
      unfold MapCore.lt_key in L. cbn in L. unfold Name.lt in H.
      rewrite Name.antisym in L. rewrite H in L. discriminate L.
    + assert (A : SetoidList.InA MapCore.eq_key_elt (kb, vb) ((ka, va) :: a')). { apply E. left. split; reflexivity. }
      invert A as [| ? ? I]. { destruct H0; cbn in *; subst. rewrite Name.compare_refl in H. discriminate H. }
      assert (L : MapCore.lt_key (ka, va) (kb, vb)). { eapply sorted_lt; try exact I; eassumption. }
      unfold MapCore.lt_key in L. cbn in L. unfold Name.lt in H.
      rewrite Name.antisym in L. rewrite H in L. discriminate L.
  - intros x y. unfold Find. repeat rewrite <- MapCore.bindings_spec1. rewrite E. reflexivity.
Qed.
