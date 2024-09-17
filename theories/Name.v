From Coq Require
  Morphisms
  RelationClasses
  String
  .
From LinearCore Require
  Reflect
  .
From LinearCore Require Import
  Invert.



Variant name : Set :=
  | Name (head : Ascii.ascii) (tail : String.string)
  .



Definition eqb a b :=
  match a with Name ha ta =>
    match b with Name hb tb =>
      andb (Ascii.eqb ha hb) (String.eqb ta tb)
    end
  end.

Lemma spec a b
  : Reflect.Bool (a = b) (eqb a b).
Proof.
  destruct a as [ha ta]. destruct b as [hb tb]. cbn.
  destruct (Ascii.eqb_spec ha hb). 2: { constructor. intro D. invert D. apply n. reflexivity. }
  destruct (String.eqb_spec ta tb); constructor. { f_equal; assumption. }
  intro D. invert D. apply n. reflexivity.
Qed.

Lemma eqb_refl s
  : eqb s s = true.
Proof. destruct s as [head tail]. cbn. rewrite Ascii.eqb_refl. rewrite String.eqb_refl. reflexivity. Qed.

Lemma eqb_eq a b
  : a = b <-> eqb a b = true.
Proof.
  destruct a as [ha ta]. destruct b as [hb tb]. cbn. split; intro E.
  - invert E; subst. rewrite Ascii.eqb_refl. rewrite String.eqb_refl. reflexivity.
  - destruct (Ascii.eqb_spec ha hb). 2: { discriminate E. } destruct (String.eqb_spec ta tb). 2: { discriminate E. }
    f_equal; assumption.
Qed.

Lemma eqb_neq a b
  : a <> b <-> eqb a b = false.
Proof.
  destruct a as [ha ta]. destruct b as [hb tb]. cbn. split; intro N.
  - destruct (Ascii.eqb_spec ha hb). 2: { reflexivity. } destruct (String.eqb_spec ta tb). 2: { reflexivity. }
    subst. contradiction N. reflexivity.
  - intro E. invert E; subst. rewrite Ascii.eqb_refl in N. rewrite String.eqb_refl in N. discriminate N.
Qed.

Lemma eqb_sym a b
  : eqb a b = eqb b a.
Proof.
  intros. destruct (spec b a). { subst. apply eqb_refl. }
  destruct (spec a b). 2: { reflexivity. } subst. contradiction N. reflexivity.
Qed.



Definition to_string s :=
  match s with Name head tail =>
    String.String head tail
  end.

Definition from_string s :=
  match s with
  | String.EmptyString => None
  | String.String head tail => Some (Name head tail)
  end.

Lemma roundtrip s
  : from_string (to_string s) = Some s.
Proof. destruct s as [head tail]. reflexivity. Qed.



Definition compare a b :=
  match a with Name ha ta =>
    match b with Name hb tb =>
      match Ascii.compare ha hb with
      | Eq => String.compare ta tb
      | Lt => Lt
      | Gt => Gt
      end
    end
  end.

Lemma ascii_refl a
  : Ascii.compare a a = Eq.
Proof.
  destruct Ascii.compare eqn:E; [reflexivity | |]; assert (D := E);
  rewrite Ascii.compare_antisym in D; rewrite E in D; discriminate D.
Qed.

Lemma string_refl s
  : String.compare s s = Eq.
Proof.
  destruct String.compare eqn:E; [reflexivity | |]; assert (D := E);
  rewrite String.compare_antisym in D; rewrite E in D; discriminate D.
Qed.

Lemma compare_refl s
  : compare s s = Eq.
Proof. destruct s as [head tail]. cbn. rewrite ascii_refl. rewrite string_refl. reflexivity. Qed.

Lemma ascii_trans
  x y (Lxy : Ascii.compare x y = Lt)
  z (Lyz : Ascii.compare y z = Lt)
  : Ascii.compare x z = Lt.
Proof.
  unfold Ascii.compare in *.
  destruct (BinNat.N.compare_spec (Ascii.N_of_ascii x) (Ascii.N_of_ascii y)); try discriminate Lxy; clear Lxy.
  destruct (BinNat.N.compare_spec (Ascii.N_of_ascii y) (Ascii.N_of_ascii z)); try discriminate Lyz; clear Lyz.
  eapply BinNat.N.lt_strorder; eassumption.
Qed.

Lemma string_trans
  x y (Lxy : String.compare x y = Lt)
  z (Lyz : String.compare y z = Lt)
  : String.compare x z = Lt.
Proof.
  generalize dependent z. generalize dependent y. induction x as [| hx tx]; intros;
  (destruct y as [| hy ty]; [discriminate Lxy |]; destruct z as [| hz tz]; [discriminate Lyz |]). { reflexivity. }
  cbn in *. destruct (Ascii.compare hx hy) eqn:Axy. 3: { discriminate Lxy. } { apply Ascii.compare_eq_iff in Axy.
    subst. destruct (Ascii.compare hy hz) eqn:Ayz. { eapply IHtx; eassumption. } { reflexivity. } assumption. }
  destruct (Ascii.compare hy hz) eqn:Ayz. 3: { discriminate Lyz. } {
    apply Ascii.compare_eq_iff in Ayz. subst. rewrite Axy. reflexivity. }
  erewrite ascii_trans; eassumption.
Qed.

Lemma trans
  x y (Lxy : compare x y = Lt)
  z (Lyz : compare y z = Lt)
  : compare x z = Lt.
Proof.
  destruct x as [hx tx]. destruct y as [hy ty]. destruct z as [hz tz]. cbn in *.
  destruct (Ascii.compare hx hy) eqn:Axy. 3: { discriminate Lxy. } {
    apply Ascii.compare_eq_iff in Axy. subst.
    destruct Ascii.compare eqn:Ayz. 2: { reflexivity. } 2: { discriminate Lyz. } eapply string_trans; eassumption. }
  destruct (Ascii.compare hy hz) eqn:Ayz. 3: { discriminate Lyz. } {
    apply Ascii.compare_eq_iff in Ayz. subst. rewrite Axy. reflexivity. }
  erewrite ascii_trans; eassumption.
Qed.

Lemma antisym a b
  : compare a b = CompOpp (compare b a).
Proof.
  destruct a as [ha ta]. destruct b as [hb tb]. cbn. rewrite Ascii.compare_antisym. rewrite String.compare_antisym.
  destruct (Ascii.compare hb ha) eqn:A; reflexivity.
Qed.

Lemma compare_eq a b
  : compare a b = Eq <-> a = b.
Proof.
  destruct a as [ha ta]. destruct b as [hb tb]. cbn. split; intro E.
  - destruct (Ascii.compare ha hb) eqn:A; try discriminate E.
    apply Ascii.compare_eq_iff in A. apply String.compare_eq_iff in E. f_equal; assumption.
  - invert E; subst. rewrite ascii_refl. apply string_refl.
Qed.



Definition leb a b :=
  match compare a b with
  | Lt | Eq => true
  | Gt => false
  end.
Arguments leb a b/.



Lemma eq_dec (x y : name)
  : {x = y} + {x <> y}.
Proof.
  destruct x as [hx tx]. destruct y as [hy ty].
  destruct (Ascii.eqb_spec hx hy). 2: { right. intro D. invert D. apply n. reflexivity. }
  destruct (String.eqb_spec tx ty); [left | right]. 2: { intro D. invert D. apply n. reflexivity. }
  f_equal; assumption.
Qed.



Definition t := name.
Arguments t/.

Definition lt a b := compare a b = Lt.
Arguments lt a b/.

Definition eq := @eq t.
Arguments eq/ a b : rename.

Lemma eq_equiv
  : RelationClasses.Equivalence eq.
Proof.
  constructor.
  - constructor.
  - unfold RelationClasses.Symmetric. intros. cbn in *. subst. reflexivity.
  - unfold RelationClasses.Transitive. intros. cbn in *. subst. reflexivity.
Qed.

Lemma lt_strorder
  : RelationClasses.StrictOrder lt.
Proof.
  constructor.
  - unfold RelationClasses.Irreflexive. unfold RelationClasses.complement.
    unfold RelationClasses.Reflexive. intros. cbn in *. rewrite compare_refl in H. discriminate H.
  - unfold RelationClasses.Transitive. intros. eapply trans; eassumption.
Qed.

Lemma lt_compat
  : Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) lt.
Proof.
  unfold Morphisms.Proper. unfold Morphisms.respectful. cbn in *.
  intros x' x Ex y' y Ey. subst. split; intros; assumption.
Qed.

Lemma compare_spec x y
  : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Proof.
  intros. cbn. rewrite antisym. destruct (compare y x) eqn:Ec; constructor; try reflexivity.
  apply compare_eq in Ec. subst. reflexivity.
Qed.

Lemma leb_total x y
  : leb x y = true \/ leb y x = true.
Proof.
  destruct x as [hx tx]. destruct y as [hy ty]. cbn. rewrite Ascii.compare_antisym.
  destruct (Ascii.compare hy hx) eqn:Ea; [| right | left]; try reflexivity.
  rewrite String.compare_antisym. destruct (String.compare ty tx) eqn:Es; [left | right | left]; reflexivity.
Qed.
