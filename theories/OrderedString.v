From Coq Require
  String
  .



Definition t : Set := String.string.
Arguments t/.

Definition compare := String.compare.
Arguments compare/.

Definition lt (a b : String.string) := compare a b = Lt.
Arguments lt a b/.

Definition eq := @Logic.eq String.string.
Arguments eq/.

Definition eq_equiv := @RelationClasses.eq_equivalence String.string.

Lemma ascii_compare_refl x : Ascii.compare x x = Eq. Proof. apply BinNat.N.compare_refl. Qed.

Lemma compare_refl x : compare x x = Eq. Proof.
  induction x; cbn. { reflexivity. } rewrite ascii_compare_refl. exact IHx.
Qed.

Definition compare_antisym s1 s2 : compare s1 s2 = CompOpp (compare s2 s1).
Proof. apply String.compare_antisym. Qed.

Lemma lt_irrefl : RelationClasses.Irreflexive lt. Proof.
  intros s L. unfold lt in L. assert (G := L).
  rewrite compare_antisym in G. rewrite L in G. discriminate G.
Qed.

Lemma ascii_lt_trans : RelationClasses.Transitive (fun a b => Ascii.compare a b = Lt). Proof.
  intros x y z Lxy Lyz. unfold Ascii.compare in *. apply -> BinNat.N.compare_lt_iff in Lxy.
  apply -> BinNat.N.compare_lt_iff in Lyz. apply BinNat.N.compare_lt_iff.
  eapply BinNat.N.lt_trans; eassumption.
Qed.

Lemma lt_trans : RelationClasses.Transitive lt. Proof.
  intros x y z Lxy Lyz. unfold lt in *. generalize dependent y.
  generalize dependent x. induction z as [| z zs IHz]; intros. {
    destruct y; discriminate Lyz. }
  destruct y as [| y ys]. { destruct x; discriminate Lxy. }
  destruct x as [| x xs]. { reflexivity. } cbn in *. destruct (Ascii.compare x y) eqn:Exy.
  - apply Ascii.compare_eq_iff in Exy as ->. destruct (Ascii.compare y z) eqn:Eyz.
    + apply Ascii.compare_eq_iff in Eyz as ->. eapply IHz; eassumption.
    + reflexivity.
    + discriminate Lyz.
  - destruct (Ascii.compare y z) eqn:Eyz.
    + apply Ascii.compare_eq_iff in Eyz as ->. rewrite Exy. reflexivity.
    + erewrite ascii_lt_trans. { reflexivity. } { eassumption. } eassumption.
    + discriminate Lyz.
  - discriminate Lxy.
Qed.

Lemma lt_strorder : RelationClasses.StrictOrder lt.
Proof. split. { exact lt_irrefl. } exact lt_trans. Qed.

Lemma lt_compat : Morphisms.Proper
  (Morphisms.respectful eq (Morphisms.respectful eq iff))
  OrderedString.lt.
Proof.
  unfold Morphisms.Proper. unfold Morphisms.respectful.
  intros x y -> x' y' ->. reflexivity.
Qed.

Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y). Proof.
  destruct (compare x y) eqn:E; constructor; cbn.
  - apply String.compare_eq_iff. exact E.
  - exact E.
  - rewrite compare_antisym. rewrite E. reflexivity.
Qed.

Lemma eq_dec x y : {eq x y} + {~eq x y}.
Proof. destruct (String.eqb_spec x y); [left | right]; assumption. Qed.
