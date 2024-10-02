From LinearCore Require
  Reflect
  .



Variant ownership : Set :=
  | Owned
  | Referenced
  .

Definition eq a b :=
  match a, b with
  | Owned, Owned
  | Referenced, Referenced => true
  | _, _ => false
  end.

Lemma eq_spec a b
  : Reflect.Bool (a = b) (eq a b).
Proof. destruct a; destruct b; constructor; try reflexivity; intro D; discriminate D. Qed.

Definition owned ownership := match ownership with Owned => true | Referenced => false end.
Arguments owned ownership/.
