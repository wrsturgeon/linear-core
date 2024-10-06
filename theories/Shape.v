From Equations Require Import
  Equations
  .
From LinearCore Require
  Context
  Map
  Reflect
  Term
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



Variant shape : Set :=
  | Resource
  | Function
  .



Inductive ShapeOf : Term.term -> shape -> Prop :=
  | Ctr ctor
      : ShapeOf (Term.Ctr ctor) Resource
  | App {curried} (curried_resource : ShapeOf curried Resource) argument
      : ShapeOf (Term.App curried argument) Resource
  | Cas pattern body_if_match other_cases
      : ShapeOf (Term.Cas pattern body_if_match other_cases) Function
  .

Lemma det {t s1} (S1 : ShapeOf t s1) {s2} (S2 : ShapeOf t s2)
  : s1 = s2.
Proof. generalize dependent s2. induction S1; intros; invert S2; reflexivity. Qed.



Fixpoint shape_of t :=
  match t with
  | Term.Ctr _ => Some Resource
  | Term.App curried argument =>
      match shape_of curried with
      | Some Resource => Some Resource
      | _ => None
      end
  | Term.Cas _ _ _ => Some Function
  | _ => None
  end.

Lemma shape_spec t
  : Reflect.Option (ShapeOf t) (shape_of t).
Proof.
  induction t; cbn; try solve [constructor; intros s C; invert C].
  - constructor. constructor.
  - destruct IHt1. 2: { constructor. intros s C. invert C. apply N in curried_resource as []. }
    destruct x; constructor. { constructor. exact Y. }
    intros s C. invert C. assert (D := det Y curried_resource). discriminate D.
  - constructor. constructor.
Qed.

Lemma shape_iff t s
  : ShapeOf t s <-> shape_of t = Some s.
Proof.
  destruct (shape_spec t).
  - split. { intro S. destruct (det Y S). reflexivity. } intro E. invert E. exact Y.
  - split. { intro S. apply N in S as []. } intro D. discriminate D.
Qed.



Variant ShapeOrRef context : Term.term -> shape -> Prop :=
  | RRef {symlink real_name looked_up}
      (follow_references : Context.FollowReferences context symlink real_name looked_up)
      {shape} (shaped : ShapeOf looked_up shape)
      : ShapeOrRef context (Term.Var symlink Ownership.Referenced) shape
  | RDel {term shape} (shaped : ShapeOf term shape)
      : ShapeOrRef context term shape
  .

Lemma det_ref {c1 t s1} (S1 : ShapeOrRef c1 t s1) {c2}
  (Ec : Map.Eq c1 c2) {s2} (S2 : ShapeOrRef c2 t s2)
  : s1 = s2.
Proof.
  invert S1. 2: { invert S2. { invert shaped. } eapply det; eassumption. }
  invert S2. 2: { invert shaped0. }
  destruct (Context.follow_references_det follow_references Ec eq_refl follow_references0) as [<- <-]. eapply det; eassumption.
Qed.

Lemma eq_ref {c1 t s1} (S1 : ShapeOrRef c1 t s1) {c2}
  (Ec : Map.Eq c1 c2) {s2} (Es : s1 = s2)
  : ShapeOrRef c2 t s2.
Proof. invert S1; econstructor; try eassumption. eapply Context.follow_references_eq; try eassumption; reflexivity. Qed.

Lemma or_ref {t s} (S : ShapeOf t s) context
  : ShapeOrRef context t s.
Proof. generalize dependent context. induction S; intros; repeat constructor; exact S. Qed.



Definition shape_or_ref (context : Context.context) (t : Term.term) :=
  match t with
  | Term.Var symlink Ownership.Referenced =>
      match Context.follow_references context symlink with
      | None => None
      | Some (real_name, looked_up) => shape_of looked_up
      end
  | _ => shape_of t
  end.

Lemma shape_or_ref_spec context t
  : Reflect.Option (ShapeOrRef context t) (shape_or_ref context t).
Proof.
  unfold shape_or_ref. destruct (shape_spec t).
  - destruct t; try destruct ownership; try solve [constructor; apply or_ref; exact Y]. invert Y.
  - destruct t; try destruct ownership; try solve [constructor; intros s C; invert C; apply N in shaped as []].
    destruct (Context.follow_references_spec context name) as [[k v] |]; cbn in *.
    + destruct (shape_spec v); constructor. { econstructor. { exact Y. } exact Y0. }
      intros s C. invert C. 2: { invert shaped. }
      destruct (Context.follow_references_det Y (Map.eq_refl _) eq_refl follow_references) as [<- <-]. apply N0 in shaped as [].
    + constructor. intros s C. invert C. 2: { invert shaped. } apply (N0 (_, _)) in follow_references as [].
Qed.
