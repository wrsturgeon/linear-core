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



Inductive ShapeOrRef context : Term.term -> shape -> Prop :=
  | RCtr ctor
      : ShapeOrRef context (Term.Ctr ctor) Resource
  | RRef {name term} (F : Map.Find context name term)
      {without_self} (R : Map.Remove name context without_self)
      {shape} (S : ShapeOrRef without_self term shape)
      : ShapeOrRef context (Term.Var name Ownership.Referenced) shape
  | RApp {curried} (curried_resource : ShapeOf curried Resource) argument
      : ShapeOrRef context (Term.App curried argument) Resource
  | RCas pattern body_if_match other_cases
      : ShapeOrRef context (Term.Cas pattern body_if_match other_cases) Function
  .

Lemma det_ref {c1 t s1} (S1 : ShapeOrRef c1 t s1) {c2}
  (Ec : Map.Eq c1 c2) {s2} (S2 : ShapeOrRef c2 t s2)
  : s1 = s2.
Proof.
  generalize dependent s2. generalize dependent c2. induction S1; intros; try solve [invert S2; reflexivity].
  invert S2. eapply IHS1. 2: { apply Ec in F0. destruct (Map.find_det F F0). exact S. }
  intros k v. destruct R as [D R]. cbn in R. rewrite R.
  destruct R0 as [D0 R0]. cbn in R0. rewrite R0. cbn in Ec. rewrite Ec. reflexivity.
Qed.

Lemma eq_ref {c1 t s1} (S1 : ShapeOrRef c1 t s1) {c2}
  (Ec : Map.Eq c1 c2) {s2} (Es : s1 = s2)
  : ShapeOrRef c2 t s2.
Proof.
  generalize dependent s2. generalize dependent c2. induction S1; intros; subst; try solve [constructor].
  - econstructor. { apply Ec. exact F. } 2: { exact S1. }
    split. { eexists. apply Ec. exact F. } destruct R as [D R]. cbn in R.
    intros k v. rewrite R. cbn in Ec. rewrite Ec. reflexivity.
  - constructor. exact curried_resource.
Qed.



Equations shape_or_ref (context : Context.context) (t : Term.term)
  : option shape by wf (Map.cardinality context) lt :=
  shape_or_ref _ (Term.Ctr _) := Some Resource;
  shape_or_ref context (Term.Var name Ownership.Referenced) with Map.found_dec context name => {
  | Map.NotFound => None
  | @Map.Found term _ => shape_or_ref (Map.remove name context) term };
  shape_or_ref _ (Term.App curried argument) :=
    match shape_of curried with Some Resource => Some Resource | _ => None end;
  shape_or_ref _ (Term.Cas _ _ _) := Some Function;
  shape_or_ref _ _ := None.
Next Obligation.
  clear shape_or_ref. rewrite Map.cardinality_remove. apply Map.find_iff in Y as E. rewrite E. clear E.
  unfold Map.cardinality. rewrite MapCore.cardinal_spec. apply MapCore.bindings_spec1 in Y.
  remember (MapCore.bindings context) as b eqn:Eb; clear context Eb. destruct b. { invert Y. }
  cbn. apply PeanoNat.Nat.lt_succ_diag_r. Qed.
Fail Next Obligation.

Lemma shape_or_ref_spec context t
  : Reflect.Option (ShapeOrRef context t) (shape_or_ref context t).
Proof.
  funelim (shape_or_ref context t).
  - constructor. constructor.
  - constructor. intros s S. invert S.
  - destruct (shape_of curried) eqn:E. 2: {
      constructor. intros s S. invert S. apply shape_iff in curried_resource.
      rewrite E in curried_resource. discriminate curried_resource. }
    destruct s; constructor. { constructor. apply shape_iff. exact E. }
    intros s S. invert S. apply shape_iff in curried_resource. rewrite E in curried_resource. invert curried_resource.
  - constructor. intros s S. invert S.
  - constructor. constructor.
  - destruct H; constructor. { econstructor. { exact Y. } { apply Map.remove_remove. eexists. exact Y. } exact Y0. }
    intros s S. invert S. eapply N. destruct (Map.find_det Y F). eapply eq_ref. { exact S0. } 2: { reflexivity. }
    eapply Map.remove_det. { exact R. } { reflexivity. } { apply Map.eq_refl. } apply Map.remove_remove. eexists. exact Y.
  - constructor. intros s S. invert S. apply N in F as [].
Qed.



Lemma or_ref {t s} (S : ShapeOf t s) context
  : ShapeOrRef context t s.
Proof. generalize dependent context. induction S; intros. { constructor. } { constructor. exact S. } constructor. Qed.
