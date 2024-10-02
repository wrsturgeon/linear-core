From LinearCore Require
  Fuel
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



Fixpoint shape_or_ref fuel context t :=
  match fuel with Fuel.Stop => Halt.OutOfFuel | Fuel.Continue fuel =>
    match t with
    | Term.Ctr _ => Halt.Return Resource
    | Term.Var name Ownership.Referenced =>
        match Map.find context name with None => Halt.Exit | Some term =>
          shape_or_ref fuel (Map.remove name context) term
        end
    | Term.App curried argument =>
        match shape_of curried with
        | Some Resource => Halt.Return Resource
        | _ => Halt.Exit
        end
    | Term.Cas _ _ _ => Halt.Return Function
    | _ => Halt.Exit
    end
  end.

Lemma shape_or_ref_spec fuel context t
  : Reflect.Halt (ShapeOrRef context t) (shape_or_ref fuel context t).
Proof.
  generalize dependent t. generalize dependent context. induction fuel. { constructor. }
  destruct t; cbn; try solve [constructor; intros s C; invert C].
  - constructor. constructor.
  - destruct ownership. { constructor. intros s S. invert S. }
    destruct (Map.find_spec context name). 2: { constructor. intros s C. invert C. apply N in F as []. }
    destruct (IHfuel (Map.remove name context) x); constructor.
    + econstructor. { exact Y. } 2: { exact Y0. } apply Map.remove_remove. eexists. exact Y.
    + intros s C. invert C. destruct (Map.find_det Y F). eapply N. eapply eq_ref. { exact S. } 2: { reflexivity. }
      intros k v. destruct R as [D R]. cbn in R. rewrite R. symmetry. apply Map.remove_if_present_remove.
  - destruct (shape_spec t1). 2: { constructor. intros s C. invert C. apply N in curried_resource as []. }
    destruct x; constructor. { constructor. exact Y. }
    intros s C. invert C. assert (D := det Y curried_resource). discriminate D.
  - constructor. constructor.
Qed.



Lemma or_ref {t s} (S : ShapeOf t s) context
  : ShapeOrRef context t s.
Proof. generalize dependent context. induction S; intros. { constructor. } { constructor. exact S. } constructor. Qed.
