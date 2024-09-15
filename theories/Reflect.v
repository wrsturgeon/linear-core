From LinearCore Require Import
  Invert
  .



Variant Reflect (P : Prop) : bool -> Prop :=
  | T (Y : P)
      : Reflect P true
  | F (N : ~P)
      : Reflect P false
  .



Variant ReflectOpt {T} (P : T -> Prop) : option T -> Prop :=
  | S x (Y : P x)
      : ReflectOpt P (Some x)
  | N (N : forall x, ~P x)
      : ReflectOpt P None
  .



Lemma iff P b (R : Reflect P b)
  : P <-> b = true.
Proof. invert R; split; intro C; try tauto. discriminate C. Qed.

Lemma niff P b (R : Reflect P b)
  : ~P <-> b = false.
Proof. invert R; split; intro C; try tauto. discriminate C. Qed.

Lemma det
  P p (Rp : Reflect P p)
  Q q (Rq : Reflect Q q)
  (E : P <-> Q)
  : p = q.
Proof. invert Rp; invert Rq; tauto. Qed.

Lemma and
  P p (Rp : Reflect P p)
  Q q (Rq : Reflect Q q)
  : Reflect (P /\ Q) (p && q).
Proof. invert Rp; invert Rq; constructor; tauto. Qed.

Lemma or
  P p (Rp : Reflect P p)
  Q q (Rq : Reflect Q q)
  : Reflect (P \/ Q) (p || q).
Proof. invert Rp; invert Rq; constructor; tauto. Qed.



Lemma opt_eq {T}
  P Q (E : forall x : T, P x <-> Q x) opt
  : ReflectOpt P opt <-> ReflectOpt Q opt.
Proof. split; intro R; (destruct R; constructor; [apply E; assumption |]); intros x C; eapply N0; apply E; exact C. Qed.
