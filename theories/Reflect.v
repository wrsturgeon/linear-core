From LinearCore Require Import
  Invert
  .



Variant Bool (P : Prop) : bool -> Prop :=
  | T (Y : P)
      : Bool P true
  | F (N : ~P)
      : Bool P false
  .



Variant Option {T} (P : T -> Prop) : option T -> Prop :=
  | S x (Y : P x)
      : Option P (Some x)
  | N (N : forall x, ~P x)
      : Option P None
  .



Lemma bool_iff {P b} (R : Bool P b)
  : P <-> b = true.
Proof. invert R; split; intro C; try tauto. discriminate C. Qed.

Lemma bool_niff {P b} (R : Bool P b)
  : ~P <-> b = false.
Proof. invert R; split; intro C; try tauto. discriminate C. Qed.

Lemma bool_eq
  {Q P} (E : P <-> Q) b
  : Bool P b <-> Bool Q b.
Proof. split; intro R; (destruct R; constructor; [apply E; exact Y |]); intro C; apply N0; apply E; exact C. Qed.

Lemma bool_det
  {P p} (Rp : Bool P p)
  {Q q} (Rq : Bool Q q)
  (E : P <-> Q)
  : p = q.
Proof. invert Rp; invert Rq; tauto. Qed.

Lemma and
  {P p} (Rp : Bool P p)
  {Q q} (Rq : Bool Q q)
  : Bool (P /\ Q) (p && q).
Proof. invert Rp; invert Rq; constructor; tauto. Qed.

Lemma or
  {P p} (Rp : Bool P p)
  {Q q} (Rq : Bool Q q)
  : Bool (P \/ Q) (p || q).
Proof. invert Rp; invert Rq; constructor; tauto. Qed.



Lemma option_eq {T}
  {Q P} (E : forall x : T, P x <-> Q x) opt
  : Option P opt <-> Option Q opt.
Proof. split; intro R; (destruct R; constructor; [apply E; assumption |]); intros x C; eapply N0; apply E; exact C. Qed.

Lemma option_if {T P opt} (R : @Option T P opt) t (E : opt = Some t)
  : P t.
Proof. destruct R. { invert E. exact Y. } discriminate E. Qed.
