From LinearCore Require
  MapCore
  Reflect
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

Lemma find_dec {T} (m : to T) k
  : {exists v, Find m k v} + {forall v, ~Find m k v}.
Proof.
  destruct (find m k) as [v |] eqn:F; [left | right].
  - exists v. apply find_iff. exact F.
  - intros v C. apply find_iff in C. rewrite F in C. discriminate C.
Qed.

Variant found {T} (m : to T) k : Type :=
  | Found (v : T) (Y : Find m k v)
  | NotFound (N : forall v, ~Find m k v)
  .

Lemma found_dec {T} (m : to T) k : found m k. Proof.
  destruct (find m k) as [v |] eqn:F; [eleft | right]. { apply find_iff. exact F. }
  intros v C. apply find_iff in C. rewrite F in C. discriminate C.
Defined.



Definition ForAll {T} (P : String.string -> T -> Prop) (m : to T) : Prop :=
  forall k v (F : Find m k v), P k v.
Arguments ForAll {T} P m/.

Definition for_all : forall T, (String.string -> T -> bool) -> to T -> bool := @MapCore.for_all.
Arguments for_all {T} p m : rename, simpl never.

Lemma for_all_spec {T P p} (R : forall k (v : T), Reflect.Bool (P k v) (p k v)) m
  : Reflect.Bool (ForAll P m) (for_all p m).
Proof.
  cbn in *. unfold Find. rewrite MapCore.for_all_spec. eapply (@Reflect.bool_eq (forall k v
    (F : SetoidList.InA MapCore.eq_key_elt (k, v) (MapCore.bindings m)), P k v)). {
    split; intros H k v; [rewrite MapCore.bindings_spec1 | rewrite <- MapCore.bindings_spec1]; apply H. }
  remember (MapCore.bindings m) as bindings eqn:Eb; clear m Eb.
  induction bindings as [| [k v] tail IH]; cbn in *. { constructor. intros k v C. invert C. }
  destruct (R k v); cbn in *. 2: { constructor. intro C. apply N. apply C. left. split; reflexivity. }
  destruct IH; constructor.
  - intros k' v' I. invert I. 2: { apply Y0. assumption. } invert H0; cbn in *; subst. exact Y.
  - intro C. apply N. intros k' v' I. apply C. right. exact I.
Qed.



Definition Any {T} (P : String.string -> T -> Prop) (m : to T) : Prop :=
  exists k v, Find m k v /\ P k v.
Arguments Any {T} P m/.

Definition any : forall T, (String.string -> T -> bool) -> to T -> bool := @MapCore.exists_.
Arguments any {T} p m : rename, simpl never.

Lemma any_spec {T P p} (R : forall k (v : T), Reflect.Bool (P k v) (p k v)) m
  : Reflect.Bool (Any P m) (any p m).
Proof.
  cbn in *. unfold Find. rewrite MapCore.exists_spec. eapply (@Reflect.bool_eq (exists k v,
    SetoidList.InA MapCore.eq_key_elt (k, v) (MapCore.bindings m) /\ P k v)). {
    split; (intros [k [v [M Pkv]]]; exists k; exists v; split; [| exact Pkv]); apply MapCore.bindings_spec1; exact M. }
  remember (MapCore.bindings m) as bindings eqn:Eb; clear m Eb.
  induction bindings as [| [k v] tail IH]; cbn in *. { constructor. intros [k [v [C Pkv]]]. invert C. }
  destruct (R k v); cbn in *. { constructor. exists k. exists v. split. 2: { exact Y. } left. split; reflexivity. }
  destruct IH; constructor. { destruct Y as [k' [v' [M Pkv]]]. exists k'. exists v'. split. 2: { exact Pkv. } right. exact M. }
  intros [k' [v' [M Pkv]]]. invert M. { destruct H0; cbn in *; subst. apply N in Pkv as []. }
  apply N0. exists k'. exists v'. split. { assumption. } exact Pkv.
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

Definition singleton : forall T, String.string -> T -> to T := @MapCore.singleton.
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
Definition overriding_add : forall T, String.string -> T -> to T -> to T := @MapCore.add.
Arguments overriding_add {T} k v m : simpl never.

Definition set_add k := overriding_add k tt.
Arguments set_add k/ m.

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
  - intro F. apply MapCore.find_spec in F. destruct (String.eqb_spec x k); [left | right].
    + subst. split. { reflexivity. } unfold overriding_add in F.
      rewrite MapCore.add_spec1 in F. { invert F. subst. reflexivity. }
    + rewrite MapCore.add_spec2 in F. 2: { symmetry. assumption. } split. { assumption. } apply MapCore.find_spec. exact F.
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
  - intros [y F]. apply MapCore.find_spec in F. destruct (String.eqb_spec x k); [left | right]. { assumption. }
    rewrite MapCore.add_spec2 in F. 2: { symmetry. assumption. } eexists. apply MapCore.find_spec. exact F.
  - intros [-> | [y F]]. { eexists. apply MapCore.find_spec. apply MapCore.add_spec1. }
    destruct (String.eqb_spec x k). { subst. eexists. apply MapCore.find_spec. apply MapCore.add_spec1. }
    eexists. apply MapCore.find_spec. rewrite MapCore.add_spec2. 2: { symmetry. assumption. }
    apply MapCore.find_spec. exact F.
Qed.

Lemma add_overriding {T} {k v} {m : to T} (A : AgreeOn k v m)
  : Add k v m (overriding_add k v m).
Proof.
  cbn. intros. rewrite find_overriding_add. split; (intros [[-> ->] | F]; [left; split; reflexivity |]).
  - destruct F as [N F]. right. exact F.
  - destruct (String.eqb_spec x k). { subst. left. split. { reflexivity. } apply A. exact F. }
    right. split. { assumption. } exact F.
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
    destruct (String.eqb_spec x k); subst; eexists; apply O; [left | right]. { split; reflexivity. } split; eassumption.
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
  destruct (String.eqb_spec x k). { eexists. apply O. left. split. { assumption. } reflexivity. }
  eexists. apply O. right. split. { assumption. } exact F.
Qed.



Definition RemoveIfPresent {T} k (m m' : to T) : Prop :=
  forall x y, (Find m' x y <-> (x <> k /\ Find m x y)).
Arguments RemoveIfPresent {T} k m m'/.

Definition remove := @MapCore.remove.
Arguments remove {T} k m : rename, simpl never.

Lemma remove_if_present_remove {T} k (m : to T)
  : RemoveIfPresent k m (remove k m).
Proof.
  cbn. intros. rewrite find_iff. unfold find. unfold remove. destruct (String.eqb_spec k x).
  - subst. rewrite MapCore.remove_spec1. split. { intro D. discriminate D. } intros [C _]. contradiction C. reflexivity.
  - rewrite MapCore.remove_spec2. 2: { assumption. } fold (find m x). rewrite <- find_iff.
    split. { intro F. split. { symmetry. assumption. } exact F. } intros [_ F]. exact F.
Qed.

Lemma remove_if_present_eq {T k1} {m1 m1' : to T} (R1 : RemoveIfPresent k1 m1 m1')
  {k2} (Ek : k1 = k2)
  {m2} (Em : Eq m1 m2)
  {m2'} (Em' : Eq m1' m2')
  : RemoveIfPresent k2 m2 m2'.
Proof. subst. cbn in *. intros x y. rewrite <- Em'. rewrite R1. rewrite Em. reflexivity. Qed.

Lemma remove_if_present_det {T k1} {m1 m1' : to T} (R1 : RemoveIfPresent k1 m1 m1')
  {k2} (Ek : k1 = k2)
  {m2} (Em : Eq m1 m2)
  {m2'} (R2 : RemoveIfPresent k2 m2 m2')
  : Eq m1' m2'.
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
  {m2} (Em : Eq m1 m2)
  {m2'} (R2 : Remove k2 m2 m2')
  : Eq m1' m2'.
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

Definition override {T} {_ : String.string} (a b : option T) :=
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



Definition Reflect (P : String.string -> Prop) (p : set) : Prop :=
  forall x, (In p x <-> P x).
Arguments Reflect P p/.



(*
Definition Map {X Y} (f : String.string -> X -> Y) m m' : Prop :=
  forall k, (
    (forall v (F : Find m k v), Find m' k (f k v)) /\
    (forall (N : ~In m k) (I : In m' k), False)
  ).
Arguments Map {X Y} f m m'/.
*)

Definition map : forall X Y, (String.string -> X -> Y) -> to X -> to Y := @MapCore.mapi.
Arguments map {X Y} f m : simpl never.



Definition Domain {T} (m : to T) (d : set) : Prop := forall k, In m k <-> In d k.
Arguments Domain {T} m d/.

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

Lemma in_domain {T} k (m : to T)
  : In (domain m) k <-> In m k.
Proof. rewrite <- (find_domain k tt m). split; [intros [[] F] | intro F; exists tt]; exact F. Qed.

Lemma domain_domain {T} (m : to T)
  : Domain m (domain m).
Proof. intro k. rewrite in_domain. reflexivity. Qed.



Definition fold {X Y} (f : String.string -> X -> Y -> Y) (acc : Y) (m : to X) : Y := @MapCore.fold X Y f m acc.
Arguments fold {X Y} f acc m : simpl never.



Definition Minus {T} (everything : to T) (discard : set) (subtracted : to T) : Prop :=
  forall k v, Find subtracted k v <-> (Find everything k v /\ forall (discarded : In discard k), False).
Arguments Minus {T} everything discard subtracted/.

Definition minus {T} : to T -> set -> to T := fold (fun k _ acc => remove k acc).
Arguments minus {T} everything discard/.

Lemma minus_minus {T} (everything : to T) discard
  : Minus everything discard (minus everything discard).
Proof.
  cbn. intros. unfold fold. rewrite MapCore.fold_spec. assert (Iff
    : (Find everything k v /\ (forall (discarded : exists v, Find discard k v), False)) <->
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

Definition to_self : set -> to String.string := map (fun k _ => k).
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
  {d2} (Ed : Eq d1 d2)
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
    destruct l. { invert H1. } constructor. eapply OrderedString.lt_trans. { eassumption. } invert H. assumption.
Qed.

(*
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
    invert Sb as [| [kb vb] b Sb' Lb]. destruct (OrderedString.compare_spec ka kb).
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
      invert A as [| ? ? I]. { destruct H0; cbn in *; subst. rewrite OrderedString.compare_refl in H. discriminate H. }
      assert (L : MapCore.lt_key (kb, vb) (ka, va)). { eapply sorted_lt; try exact I; eassumption. }
      unfold MapCore.lt_key in L. cbn in L. unfold OrderedString.lt in H.
      rewrite OrderedString.antisym in L. rewrite H in L. discriminate L.
    + assert (A : SetoidList.InA MapCore.eq_key_elt (kb, vb) ((ka, va) :: a')). { apply E. left. split; reflexivity. }
      invert A as [| ? ? I]. { destruct H0; cbn in *; subst. rewrite OrderedString.compare_refl in H. discriminate H. }
      assert (L : MapCore.lt_key (ka, va) (kb, vb)). { eapply sorted_lt; try exact I; eassumption. }
      unfold MapCore.lt_key in L. cbn in L. unfold OrderedString.lt in H.
      rewrite OrderedString.antisym in L. rewrite H in L. discriminate L.
  - intros x y. unfold Find. repeat rewrite <- MapCore.bindings_spec1. rewrite E. reflexivity.
Qed.
*)

Lemma eq_key_elt {T} k (v : T) li
  : SetoidList.InA MapCore.eq_key (k, v) li <-> exists v, SetoidList.InA MapCore.eq_key_elt (k, v) li.
Proof.
  induction li as [| [k' v'] tail IH]; cbn in *; (split; [intro I | intros [v'' I]]); invert I.
  - unfold MapCore.eq_key in H0. cbn in H0. subst. eexists. left. split; reflexivity.
  - apply IH in H0 as [v'' I]. eexists. right. exact I.
  - destruct H0; cbn in *; subst. left. reflexivity.
  - right. apply IH. eexists. exact H0.
Qed.

Lemma sorted_eq {T} (a b : list (_ * T))
  (Sa : Sorted.Sorted MapCore.lt_key a) (NDa : SetoidList.NoDupA MapCore.eq_key a)
  (Sb : Sorted.Sorted MapCore.lt_key b) (NDb : SetoidList.NoDupA MapCore.eq_key b)
  : (a = b) <-> (forall kv, SetoidList.InA MapCore.eq_key_elt kv a <-> SetoidList.InA MapCore.eq_key_elt kv b).
Proof.
  split; intro E. { rewrite E. reflexivity. }
  generalize dependent b. generalize dependent NDa. induction Sa as [| [ka va] a' Sa' IH La']; intros; cbn in *. {
    destruct b. { reflexivity. } eassert (I : SetoidList.InA MapCore.eq_key_elt p (p :: b)). {
      left. split; reflexivity. } apply E in I. invert I. }
  invert NDa as [| ? ? Na' NDa']. specialize (IH NDa'). invert NDb as [| [kb vb] b' Nb' NDb']. {
    eassert (I : SetoidList.InA MapCore.eq_key_elt (ka, va) ((ka, va) :: a')). {
      left. split; reflexivity. } apply E in I. invert I. }
  invert Sb as [| ? ? Sb' Lb']. specialize (IH _ Sb' NDb'). destruct (OrderedString.compare_spec ka kb) as [Ek | Lk | Gk].
  - cbn in Ek. subst. rename kb into k. assert (I : SetoidList.InA MapCore.eq_key_elt
      (k, va) ((k, va) :: a')). { left. split; reflexivity. }
    apply E in I. invert I. 2: { contradiction Nb'. apply eq_key_elt. eexists. eassumption. }
    destruct H0 as [_ Ev]; cbn in *; subst. f_equal. apply IH. intros [k' v'].
    destruct (String.eqb_spec k' k). { subst. split; intro I; [contradiction Na' | contradiction Nb'];
      apply eq_key_elt; eexists; exact I. }
    split; intro I; eapply SetoidList.InA_cons_tl in I; apply E in I; (invert I; [| assumption]);
    destruct H0; cbn in *; subst; contradiction n; reflexivity.
  - assert (A : SetoidList.InA MapCore.eq_key_elt (ka, va) ((kb, vb) :: b')). { apply E. left. split; reflexivity. }
    invert A. { destruct H0; cbn in *; subst. rewrite OrderedString.compare_refl in Lk. discriminate Lk. }
    assert (L : MapCore.lt_key (kb, vb) (ka, va)). { eapply sorted_lt; try exact H0; eassumption. }
    unfold MapCore.lt_key in L. cbn in L. unfold OrderedString.lt in Lk.
    rewrite OrderedString.compare_antisym in L. rewrite Lk in L. discriminate L.
  - assert (A : SetoidList.InA MapCore.eq_key_elt (kb, vb) ((ka, va) :: a')). { apply E. left. split; reflexivity. }
    invert A. { destruct H0; cbn in *; subst. rewrite OrderedString.compare_refl in Gk. discriminate Gk. }
    assert (L : MapCore.lt_key (ka, va) (kb, vb)). { eapply sorted_lt; try exact H0; eassumption. }
    unfold MapCore.lt_key in L. cbn in L. unfold OrderedString.lt in Gk.
    rewrite OrderedString.compare_antisym in L. rewrite Gk in L. discriminate L.
Qed.

Lemma bindings_eq {T} a b
  : @Eq T a b <-> MapCore.bindings a = MapCore.bindings b.
Proof.
  cbn. rewrite sorted_eq; try apply MapCore.bindings_spec2; try apply MapCore.bindings_spec2w.
  unfold Find. split; [intros E [k v] | intros E k v];
  [repeat rewrite MapCore.bindings_spec1 | repeat rewrite <- MapCore.bindings_spec1]; apply E.
Qed.



(*Lemma hd_rel_filter {T} k (v : T) tail (HR : Sorted.HdRel MapCore.lt_key (k, v) tail) (S : Sorted.Sorted MapCore.lt_key (k, v) tail) f*)
(*  : Sorted.HdRel MapCore.lt_key (k, v) (List.filter f tail).*)
(*Proof.*)
(*  generalize dependent v. generalize dependent k.*)
(*  induction tail as [| [k v] tail IH]; intros; cbn in *. { constructor. }*)
(*  invert S. unfold MapCore.lt_key in H0; cbn in *. destruct (f (k, v)) eqn:E. { constructor. assumption. }*)
(*  - constructor.*)
(*Qed.*)

Lemma in_a_filter {T} {li : list T} {P f x} (I : SetoidList.InA P x (List.filter f li))
  : SetoidList.InA P x li.
Proof.
  generalize dependent I. induction li as [| head tail IH]; intros; cbn in *. { invert I. }
  destruct (f head) eqn:F. 2: { right. apply IH. exact I. }
  invert I; [left | right]. { assumption. } apply IH. assumption.
Qed.

Lemma sorted_filter {T} (li : list (_ * T)) (S : Sorted.Sorted MapCore.lt_key li)
  (ND : SetoidList.NoDupA MapCore.eq_key li) f
  : Sorted.Sorted MapCore.lt_key (List.filter f li).
Proof.
  induction S as [| [k v] tail S IH L]; intros; cbn in *. { constructor. }
  invert ND. specialize (IH H2). destruct (f (k, v)) eqn:E. 2: { exact IH. } constructor. { exact IH. }
  destruct (List.filter f tail) as [| [k' v'] tail'] eqn:F. { constructor. }
  invert IH. constructor. eapply sorted_lt; [| | eassumption | |]; try eassumption.
  eapply in_a_filter. rewrite F. left. split; reflexivity.
Qed.

Lemma no_dup_filter {T} (li : list (_ * T)) (ND : SetoidList.NoDupA MapCore.eq_key li) f
  : SetoidList.NoDupA MapCore.eq_key (List.filter f li).
Proof.
  induction ND as [| [k v] tail N ND IH]; cbn in *. { constructor. }
  destruct (f (k, v)) eqn:F. 2: { exact IH. } constructor. 2: { exact IH. }
  intro C. apply N. eapply in_a_filter. exact C.
Qed.

Lemma bindings_remove {T} x (m : to T)
  : MapCore.bindings (remove x m) = List.filter (fun kv => negb (String.eqb x (fst kv))) (MapCore.bindings m).
Proof.
  apply sorted_eq. { apply MapCore.bindings_spec2. } { apply MapCore.bindings_spec2w. } {
    apply sorted_filter. { apply MapCore.bindings_spec2. } apply MapCore.bindings_spec2w. } {
    apply no_dup_filter. apply MapCore.bindings_spec2w. }
  intros [k v]. repeat rewrite MapCore.bindings_spec1.
  unfold remove. rewrite <- MapCore.find_spec. destruct (String.eqb_spec k x).
  - subst. rewrite MapCore.remove_spec1. split. { intro D. discriminate D. }
    intro I. remember (MapCore.bindings m) as b eqn:Eb; clear m Eb.
    induction b as [| [k' v'] tail IH]; cbn in *. { invert I. }
    destruct (String.eqb_spec x k'); subst; cbn in *. { apply IH. exact I. } invert I. 2: { apply IH. assumption. }
    destruct H0; cbn in *; subst. contradiction n. reflexivity.
  - rewrite MapCore.remove_spec2. 2: { intros ->. contradiction n. reflexivity. }
    rewrite MapCore.find_spec. rewrite <- MapCore.bindings_spec1.
    remember (MapCore.bindings m) as b eqn:Eb; clear m Eb.
    generalize dependent x. induction b as [| [k' v'] tail IH]; intros; cbn in *. { reflexivity. }
    destruct (String.eqb_spec x k'); subst; cbn in *.
    + rewrite <- IH. 2: { assumption. } split; intro I. 2: { right. exact I. }
      invert I. { destruct H0; cbn in *; subst. contradiction n. reflexivity. } assumption.
    + split; intro I; (invert I; [left; assumption | right]); (eapply IH; [exact n |]); assumption.
Qed.



Definition cardinality {T} : to T -> nat := MapCore.cardinal.
Arguments cardinality {T} m : simpl never.

Lemma cardinality_remove {T} (m : to T) k
  : cardinality (remove k m) =
    match find m k with
    | None => cardinality m
    | Some _ => Nat.pred (cardinality m)
    end.
Proof.
  unfold cardinality. rewrite MapCore.cardinal_spec. rewrite bindings_remove. destruct (find_spec m k).
  - rewrite MapCore.cardinal_spec. apply MapCore.bindings_spec1 in Y. assert (ND := MapCore.bindings_spec2w m).
    remember (MapCore.bindings m) as b eqn:Eb; clear m Eb; rename b into li.
    induction ND as [| [k' v'] tail N ND IH]; intros; cbn in *. { reflexivity. }
    destruct (String.eqb_spec k k'); subst; cbn in *. 2: {
      invert Y. { destruct H0; cbn in *; subst. contradiction n. reflexivity. } rewrite IH. 2: { assumption. }
      apply PeanoNat.Nat.succ_pred. intro E. destruct H0; discriminate E. }
    invert Y. 2: { contradiction N. apply eq_key_elt. eexists. eassumption. }
    destruct H0 as [_ E]; cbn in *; subst. clear IH.
    rewrite List.forallb_filter_id. { reflexivity. }
    generalize dependent v'. generalize dependent k'.
    induction ND as [| [k v] tail N ND IH]; intros; cbn in *. { reflexivity. }
    destruct (String.eqb_spec k' k); cbn in *. { subst. contradiction N0. left. reflexivity. }
    eapply IH. intro C. apply N0. right. exact C.
  - rewrite List.forallb_filter_id. { symmetry. apply MapCore.cardinal_spec. }
    destruct List.forallb eqn:F. { reflexivity. } assert (A : exists v, Find m k v). 2: {
      destruct A as [k' F']. apply N in F' as []. } clear N.
    assert (A : (exists v, Find m k v) <-> exists v, SetoidList.InA MapCore.eq_key_elt (k, v) (MapCore.bindings m)). {
      split; intros [v F']; exists v; apply MapCore.bindings_spec1; exact F'. } apply A; clear A.
    remember (MapCore.bindings m) as b eqn:Eb; clear m Eb; rename b into li.
    induction li as [| [k' v'] tail IH]; intros; cbn in *. { discriminate F. }
    destruct (String.eqb_spec k k'); subst; cbn in *. { eexists. left. split; reflexivity. }
    specialize (IH F) as [v IH]. exists v. right. exact IH.
Qed.



Definition Pop {T} m k (v : T) leftover : Prop :=
  Find m k v /\ RemoveIfPresent k m leftover.
Arguments Pop {T} m k v leftover/.

(* TODO: this could be made much faster if we cracked open the definition of `remove` to do it all in one pass *)
Definition pop {T} (m : to T) k := option_map (fun v => (v, remove k m)) (find m k).
Arguments pop {T} m k/.

Lemma pop_eq {T}
  {m1 : to T} {k1 v1 l1} (P1 : Pop m1 k1 v1 l1)
  {m2} (Em : Eq m1 m2)
  {k2} (Ek : k1 = k2)
  {v2} (Ev : v1 = v2)
  {l2} (El : Eq l1 l2)
  : Pop m2 k2 v2 l2.
Proof.
  subst. destruct P1 as [F1 R1]. split. { apply Em. exact F1. }
  eapply remove_if_present_eq; try reflexivity; eassumption.
Qed.

Lemma pop_det {T}
  {m1 : to T} {k1 v1 l1} (P1 : Pop m1 k1 v1 l1)
  {m2} (Em : Eq m1 m2)
  {k2} (Ek : k1 = k2)
  {v2 l2} (P2 : Pop m2 k2 v2 l2)
  : v1 = v2 /\ Eq l1 l2.
Proof.
  subst. destruct P1 as [F1 R1]. destruct P2 as [F2 R2]. apply Em in F2. split. { eapply find_det; eassumption. }
  eapply remove_if_present_det; try reflexivity; eassumption.
Qed.

Lemma pop_spec {T} (m : to T) k
  : Reflect.Option (fun pair => Pop m k (fst pair) (snd pair)) (pop m k).
Proof.
  unfold Pop. unfold pop. destruct (find_spec m k); simpl option_map; constructor; simpl fst; simpl snd.
  - split. { exact Y. } apply remove_if_present_remove.
  - intros [v leftover] [F R]; simpl fst in *; simpl snd in *. apply N in F as [].
Qed.



Definition Disjoint {A B} (a : to A) (b : to B) :=
  forall k (Ma : In a k) (Mb : In b k), False.
Arguments Disjoint {A B} a b/.

Definition disjoint {A B} (a : to A) : to B -> bool :=
  for_all (fun k v => negb (in_ a k)).
Arguments disjoint {A B} a/ b.

Lemma disjoint_spec {A B} (a : to A) (b : to B)
  : Reflect.Bool (Disjoint a b) (disjoint a b).
Proof.
  eapply Reflect.bool_eq. 2: { eapply (@for_all_spec _ (fun k _ => ~In a k)). intros k _.
    destruct (in_spec a k); constructor. { intro C. apply C. exact Y. } intro C. apply N. exact C. }
  cbn. split; intros F k.
  - intros vb Fb [va Fa]. eapply F; eexists; eassumption.
  - intros [va Fa] [vb Fb]. eapply F. { exact Fb. } eexists. exact Fa.
Qed.

Lemma in_bindings {T} (m : to T) k
  : In m k <-> List.In k (List.map fst (MapCore.bindings m)).
Proof.
  split.
  - intros [v F]. apply MapCore.bindings_spec1 in F. remember (MapCore.bindings m) as b eqn:Eb; clear m Eb.
    generalize dependent v. generalize dependent k. induction b as [| [k v] tail IH]; intros; cbn in *. { invert F. }
    invert F; [left | right]. { destruct H0; cbn in *; subst. reflexivity. } eapply IH. exact H0.
  - intro I. assert (Iff : In m k <-> exists v, SetoidList.InA MapCore.eq_key_elt (k, v) (MapCore.bindings m)).
    + split; intros [v F]; exists v; apply MapCore.bindings_spec1; exact F.
    + apply Iff. clear Iff. remember (MapCore.bindings m) as b eqn:Eb; clear m Eb. generalize dependent k.
      induction b as [| [k v] tail IH]; intros; cbn in *. { destruct I. }
      destruct I as [-> | I]. { eexists. left. split; reflexivity. }
      specialize (IH _ I) as [v' F]. eexists. right. exact F.
Qed.

Lemma not_disjoint_exists {A B} {a : to A} {b : to B} (N : forall (D : Disjoint a b), False)
  : exists k, In a k /\ In b k.
Proof.
  assert (Iff : (exists k, In a k /\ In b k) <-> exists k, (
    List.In k (List.map fst (MapCore.bindings a)) /\
    List.In k (List.map fst (MapCore.bindings b)))). {
    split; intros [k I]; exists k; repeat rewrite in_bindings in *; exact I. } apply Iff. clear Iff.
  assert (Iff : (forall (D : Disjoint a b), False) <-> forall (D : forall k
    (Ia : List.In k (List.map fst (MapCore.bindings a)))
    (Ib : List.In k (List.map fst (MapCore.bindings b))), False), False). {
    split. 2: { intros C D. apply N in D as []. }
    intros D C. apply D. intros k Ia Ib. apply in_bindings in Ia. apply in_bindings in Ib.
    eapply C; eassumption. } rewrite Iff in N. clear Iff.
  remember (MapCore.bindings a) as ba eqn:Ea; clear a Ea.
  remember (MapCore.bindings b) as bb eqn:Eb; clear b Eb.
  generalize dependent B. induction ba as [| [k v] tail IH]; intros; cbn in *. { contradiction N. intros k []. }
  destruct (List.in_dec OrderedString.eq_dec k (List.map fst bb)). { exists k. split. { left. reflexivity. } assumption. }
  edestruct IH as [K [IHa IHb]]. 2: { exists K. split. { right. exact IHa. } exact IHb. }
  intro C. apply N. intros k' [-> | I] C'. { apply n in C' as []. } eapply C; eassumption.
Qed.



Definition OneToOne {T} (m : to T) : Prop :=
  forall k1 v (F1 : Find m k1 v) k2 (F2 : Find m k2 v), k1 = k2.
Arguments OneToOne {T} m/.

Lemma one_to_one_empty {T}
  : @OneToOne T empty.
Proof. cbn. intros. invert F1. Qed.

Lemma one_to_one_singleton {T} k v
  : @OneToOne T (singleton k v).
Proof. cbn. intros. apply find_singleton in F1 as [-> ->]. apply find_singleton in F2 as [-> _]. reflexivity. Qed.

Lemma one_to_one_remove_if_present {T} {m : to T} (O2O : OneToOne m) {x m'} (R : RemoveIfPresent x m m')
  : OneToOne m'.
Proof. cbn. intros. apply R in F1 as [N1 F1]. apply R in F2 as [N2 F2]. eapply O2O; eassumption. Qed.

Lemma one_to_one_to_self m
  : OneToOne (to_self m).
Proof. cbn. intros. apply to_self_to_self in F1 as [I1 ->]. apply to_self_to_self in F2 as [I2 ->]. reflexivity. Qed.

Lemma one_to_one_overwrite {T x y m m'} (OW : @OverwriteIfPresent T x y m m')
  : OneToOne m' <-> (
    (forall k1 (N1 : k1 <> x) v (F1 : Find m k1 v) k2 (N2 : k2 <> x) (F2 : Find m k2 v), k1 = k2) /\
    (forall z (F : Find m z y), z = x)).
Proof.
  split. 2: {
    intros [O2O E]; cbn; intros. apply OW in F1 as [[-> ->] | [N1 F1]]; apply OW in F2 as [[-> E'] | [N2 F2]]; subst.
    + reflexivity.
    + symmetry. apply E. assumption.
    + apply E. assumption.
    + eapply O2O; eassumption. }
  intro O2O. split; cbn; intros. { eapply O2O; apply OW; right; split; eassumption. }
  eapply O2O; apply OW. 2: { left. split; reflexivity. }
  destruct (String.eqb_spec z x); [left | right]. { subst. split; reflexivity. } split; assumption.
Qed.

Lemma one_to_one_bulk_overwrite {T force original overwritten} (B : @BulkOverwrite T force original overwritten)
  : OneToOne overwritten <-> (
    OneToOne force /\
    (forall k1 (N1 : forall (I : In force k1), False) v (F1 : Find original k1 v)
      k2 (N2 : forall (I : In force k2), False) (F2 : Find original k2 v), k1 = k2) /\
    (forall x y (Ff : Find force x y) z (N : forall (I : In force z), False) (Fo : Find original z y), z = x)).
Proof.
  split. 2: {
    intros [O2Of [O2Oo E]]; cbn; intros. apply B in F1 as [F1 | [N1 F1]]; apply B in F2 as [F2 | [N2 F2]].
    + eapply O2Of; eassumption.
    + symmetry. eapply E; eassumption.
    + eapply E; eassumption.
    + eapply O2Oo; eassumption. }
  intro O2O. split; [| split]; cbn; intros. { eapply O2O; apply B; left; eassumption. } {
    eapply O2O; apply B; right; (split; [| eassumption]); intro I; [apply N1 | apply N2]; exact I. }
  eapply O2O; apply B. 2: { left. exact Ff. } right. split; assumption.
Qed.



Definition Invert fwd bwd : Prop :=
  forall k v, Find fwd k v <-> Find bwd v k.
Arguments Invert fwd bwd/.

Lemma invert_sym fwd bwd
  : Invert fwd bwd <-> Invert bwd fwd.
Proof. split; intros inv k v; cbn in inv; rewrite inv; reflexivity. Qed.

(*Definition invert_acc := fold (fun k v => overriding_add v k).*)
(*Arguments invert_acc/ acc fwd : rename.*)
(**)
(*Definition invert := invert_acc empty.*)
(*Arguments invert/ fwd : rename.*)
(**)
(*Lemma invert_acc_not_overridden {k v} {acc : to String.string} (F : Find acc v k) {tail}*)
(*  (N : forall k' (I : SetoidList.InA MapCore.eq_key_elt (k', v) tail), False)*)
(*  : Find (List.fold_left (fun acc kv => overriding_add (snd kv) (fst kv) acc) tail acc) v k.*)
(*Proof.*)
(*  generalize dependent acc. induction tail as [| [k' v'] tail IH]; intros; cbn in *. { exact F. }*)
(*  apply IH. { intros k'' I. eapply N. right. exact I. }*)
(*  apply find_overriding_add. right. split. 2: { exact F. } intros ->. eapply N. left. split; reflexivity.*)
(*Qed.*)
(**)
(*Lemma invert_acc_invert {acc inv_acc} (acc_inv : Invert acc inv_acc)*)
(*  {todo} (O2O : OneToOne todo) (D : Disjoint todo inv_acc) {fwd} (U : Union todo inv_acc fwd)*)
(*  : Invert fwd (invert_acc acc todo).*)
(*Proof.*)
(*  intros k v. cbn in U. rewrite U. clear fwd U.*)
(*  assert (ND := MapCore.bindings_spec2w todo). remember (MapCore.bindings todo) as b eqn:Eb.*)
(*  remember (List.rev b) as r eqn:Er. eassert (E : invert_acc _ _ = List.fold_right _ _ r); [| rewrite E; clear E]. {*)
(*    unfold invert_acc. unfold fold. rewrite MapCore.fold_spec. rewrite <- List.fold_left_rev_right.*)
(*    f_equal. { reflexivity. } subst. reflexivity. }*)
(*  assert (O2O' : forall k1 v' (F1 : SetoidList.InA MapCore.eq_key_elt (k1, v') r)*)
(*    k2 (F2 : SetoidList.InA MapCore.eq_key_elt (k2, v') r), k1 = k2). { subst. intros.*)
(*    eapply O2O; apply MapCore.bindings_spec1; apply SetoidList.InA_rev; eassumption. } clear O2O. rename O2O' into O2O.*)
(*  assert (D' : forall k vt (F : SetoidList.InA MapCore.eq_key_elt (k, vt) r) va (I : Find acc va k), False). {*)
(*    subst. intros. eapply D. 2: { eexists. apply acc_inv. exact I. }*)
(*    eexists. apply MapCore.bindings_spec1. apply SetoidList.InA_rev. exact F. } clear D. rename D' into D.*)
(*  cbn in acc_inv. rewrite <- acc_inv. clear inv_acc acc_inv. unfold Find at 1. rewrite <- MapCore.bindings_spec1.*)
(*  rewrite <- Eb. rewrite <- SetoidList.InA_rev. rewrite <- Er. apply SetoidList.NoDupA_rev in ND. 2: {*)
(*    split. { intros []. reflexivity. } { intros [] [] E. symmetry. exact E. }*)
(*    intros [] [] [] E1 E2; unfold MapCore.eq_key in *; cbn in *; subst; reflexivity. }*)
(*  rewrite <- Er in ND. clear b todo Eb Er. rename r into todo. generalize dependent acc. generalize dependent O2O.*)
(*  generalize dependent v. generalize dependent k. induction ND as [| [k v] tail N ND IH]; intros; cbn in *. {*)
(*    split. { intros [I | F]. { invert I. } exact F. } intro F. right. exact F. }*)
(*  split.*)
(*  - intro opt. apply find_overriding_add. destruct opt as [I | F].*)
(*    + invert I. { destruct H0; cbn in *; subst. left. split; reflexivity. } right. split.*)
(*      * intros ->. assert (k0 = k). { eapply O2O. { right. eassumption. } left. split; reflexivity. }*)
(*        subst. apply N. apply eq_key_elt. eexists. eassumption.*)
(*      * apply IH. { intros. eapply O2O; right; eassumption. } 2: { left. assumption. }*)
(*        intros. eapply D in I as []. right. exact F.*)
(*    + destruct (String.eqb_spec v0 v). { subst. left. split. { reflexivity. }*)
(*        destruct (String.eqb_spec k0 k). { exact Y. }*)
(*      eapply O2O. 2: { left. split; reflexivity. }*)



Definition InDomainOrRange (x : String.string) (m : to String.string) : Prop :=
  In m x \/ InRange m x.
Arguments InDomainOrRange x m/.

Definition in_domain_or_range (x : String.string) : to String.string -> bool :=
  any (fun k v => orb (String.eqb x k) (String.eqb x v)).
Arguments in_domain_or_range x m/.

Lemma in_domain_or_range_spec x m
  : Reflect.Bool (InDomainOrRange x m) (in_domain_or_range x m).
Proof.
  eapply (@Reflect.bool_eq (Any (fun k v => x = k \/ x = v) m)); [| eapply any_spec]. 2: {
    intros. destruct (String.eqb_spec x k); cbn. { constructor. left. exact e. }
    destruct (String.eqb_spec x v); constructor. { right. exact e. }
    intros [-> | ->]. { apply n. reflexivity. } apply n0. reflexivity. } split.
  - intros [[y F] | [z F]]. 2: { do 2 eexists. split. { exact F. } right. reflexivity. }
    do 2 eexists. split. { exact F. } left. reflexivity.
  - intros [k [v [F [-> | ->]]]]; [left | right]. { eexists. exact F. } eexists. exact F.
Qed.

Lemma in_domain_or_range_dec x m
  : {InDomainOrRange x m} + {~InDomainOrRange x m}.
Proof.
  destruct (in_domain_or_range x m) eqn:E; [left | right].
  - eapply Reflect.bool_iff. { apply in_domain_or_range_spec. } exact E.
  - intro I. eapply Reflect.bool_iff in I. 2: { apply in_domain_or_range_spec. }
    rewrite I in E. discriminate E.
Defined.



Definition range_acc : set -> to String.string -> set := fold (fun k v acc => overriding_add v tt acc).
Arguments range_acc acc m/.

Definition range : to String.string -> set := range_acc empty.
Arguments range m/.

Lemma find_range_acc acc m k v
  : Find (range_acc acc m) k v <-> (In acc k \/ InRange m k).
Proof.
  destruct v. assert (Iff : InRange m k <-> exists j, SetoidList.InA MapCore.eq_key_elt (j, k) (List.rev (MapCore.bindings m))). {
    split; intros [v' F]; exists v'; [apply SetoidList.InA_rev |
      apply -> SetoidList.InA_rev in F]; apply MapCore.bindings_spec1; exact F. }
  rewrite Iff; clear Iff. unfold range. unfold range_acc. unfold fold. rewrite MapCore.fold_spec.
  rewrite <- List.fold_left_rev_right. assert (ND := MapCore.bindings_spec2w m). apply SetoidList.NoDupA_rev in ND. 2: {
    split. { intros []. reflexivity. } { intros [] []. symmetry. assumption. }
    intros [] [] [] E1 E2. unfold MapCore.eq_key in *. cbn in *. subst. reflexivity. }
  remember (List.rev (MapCore.bindings m)) as b eqn:Eb; clear m Eb.
  generalize dependent acc. induction ND as [| [k' v'] tail N ND IH]; intros; cbn in *; [| split].
  - split. { intro F. left. exists tt. exact F. } intros [[[] F] | [j I]]. { exact F. } invert I.
  - intro F. apply find_overriding_add in F as [[-> _] | [N' F]]. { right. exists k'. left. split; reflexivity. }
    apply IH in F as [[[] F] | [j I]]; [left | right]. { exists tt. exact F. } exists j. right. exact I.
  - intro opt. apply find_overriding_add. destruct opt as [[[] F] | [j I]].
    + destruct (String.eqb_spec k v'); [left | right]. { subst. split; reflexivity. }
      split. { assumption. } apply IH. left. exists tt. exact F.
    + invert I. { left. destruct H0; cbn in *; subst. split; reflexivity. }
      destruct (String.eqb_spec k v'); [left | right]. { subst. split; reflexivity. }
      split. { assumption. } apply IH. right. exists j. assumption.
Qed.

Lemma find_range m k v
  : Find (range m) k v <-> InRange m k.
Proof.
  unfold range. rewrite find_range_acc. split. { intros [I | I]. { apply empty_empty in I as []. } exact I. }
  intro I. right. exact I.
Qed.

Lemma in_range m k
  : In (range m) k <-> InRange m k.
Proof. rewrite <- (find_range m k tt). split; [intros [[] F] | intro F; exists tt]; exact F. Qed.
