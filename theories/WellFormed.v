From LinearCore Require
  BoundIn
  Pattern
  .
From LinearCore Require Import
  Invert
  .



Inductive Strict : Pattern.strict -> Prop :=
  | SCtr constructor
      : Strict (Pattern.Ctr constructor)
  | SApp curried (curried_well_formed : Strict curried) argument (N : forall (B : BoundIn.Strict curried argument), False)
      : Strict (Pattern.App curried argument)
  .
Arguments Strict strict.

Fixpoint strict_acc strict_pattern :=
  match strict_pattern with
  | Pattern.Ctr constructor => Some Map.empty
  | Pattern.App curried argument =>
      match strict_acc curried with None => None | Some bound_in_curried =>
        if Map.in_ bound_in_curried argument then None else Some (Map.overriding_add argument tt bound_in_curried)
      end
  end.

Lemma strict_acc_bound_in strict_pattern bindings (E : strict_acc strict_pattern = Some bindings)
  : Map.Reflect (BoundIn.Strict strict_pattern) bindings.
Proof.
  generalize dependent bindings. induction strict_pattern; cbn in *; intros. {
    invert E. split. { intros [y F]. invert F. } intro B. invert B. }
  destruct (strict_acc strict_pattern) as [bindings' |] eqn:Es. 2: { discriminate E. }
  destruct (Map.find_spec bindings' argument); invert E. specialize (IHstrict_pattern _ eq_refl x). split.
  - intros [v F]. apply Map.find_overriding_add in F as [[-> ->] | [Nx M]]; [left | right].
    apply IHstrict_pattern. eexists. exact M.
  - intro B. apply Map.in_overriding_add. invert B; [left | right]. { reflexivity. }
    apply IHstrict_pattern. exact bound_earlier.
Qed.

Lemma strict_acc_spec strict_pattern
  : Reflect.Option (fun _ => Strict strict_pattern) (strict_acc strict_pattern).
Proof.
  induction strict_pattern; cbn in *. { constructor. constructor. }
  assert (R := strict_acc_bound_in strict_pattern). destruct IHstrict_pattern as [bindings |]. 2: {
    constructor. intros bindings S. invert S. apply N in curried_well_formed as []. exact bindings. }
  specialize (R _ eq_refl). destruct (Map.find_spec bindings argument); constructor.
  - intros bindings' S. invert S. apply N. apply R. eexists. eassumption.
  - constructor. { exact Y. } intro B. apply R in B as [y F]. apply N in F as [].
Qed.

Definition strict strict_pattern :=
  match strict_acc strict_pattern with Some _ => true | None => false end.
Arguments strict strict_pattern/.

Lemma strict_spec strict_pattern
  : Reflect.Bool (Strict strict_pattern) (strict strict_pattern).
Proof.
  unfold strict. destruct (strict_acc_spec strict_pattern); constructor. { exact Y. }
  apply N. exact Map.empty.
Qed.



Inductive MoveOrReference : Pattern.move_or_reference -> Prop :=
  | MMov strict (strict_well_formed : Strict strict)
      : MoveOrReference (Pattern.Mov strict)
  | MRef strict (strict_well_formed : Strict strict)
      : MoveOrReference (Pattern.Ref strict)
  .
Arguments MoveOrReference move_or_reference.

Definition move_or_reference pattern :=
  match pattern with Pattern.Mov strict_pattern | Pattern.Ref strict_pattern =>
    strict strict_pattern
  end.
Arguments move_or_reference pattern/.

Lemma move_or_reference_spec pattern
  : Reflect.Bool (MoveOrReference pattern) (move_or_reference pattern).
Proof.
  unfold move_or_reference. destruct pattern; destruct (strict_spec strict0); constructor;
  try (constructor; exact Y); intro C; invert C; apply N in strict_well_formed as [].
Qed.



Inductive Pattern : Pattern.pattern -> Prop :=
  | Nam name
      : Pattern (Pattern.Nam name)
  | Pat move_or_reference (move_or_reference_well_formed : MoveOrReference move_or_reference)
      : Pattern (Pattern.Pat move_or_reference)
  .
Arguments Pattern pattern.

Definition pattern patt :=
  match patt with
  | Pattern.Nam _ => true
  | Pattern.Pat patt => move_or_reference patt
  end.

Lemma pattern_spec patt
  : Reflect.Bool (Pattern patt) (pattern patt).
Proof.
  unfold pattern. destruct patt. { constructor. constructor. }
  destruct (move_or_reference_spec move_or_reference0); constructor. { constructor. exact Y. }
  intro P. apply N. invert P. assumption.
Qed.