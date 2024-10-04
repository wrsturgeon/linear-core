From Equations Require Import
  Equations
  .
From LinearCore Require
  Map
  Reflect
  Term
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



Definition context : Type := Map.to Term.term.
Arguments context/.



Inductive FollowReferences (context : context) : Term.term -> Term.term -> Prop :=
  | Ref {name term} (F : Map.Find context name term)
      {without_self} (R : Map.Remove name context without_self)
      {followed} (transitive : FollowReferences without_self term followed)
      : FollowReferences context (Term.Var name Ownership.Referenced) followed
  | Nonref {term} (N : forall name (E : term = Term.Var name Ownership.Referenced), False)
      {followed} (E : term = followed)
      : FollowReferences context term followed
  .
Arguments FollowReferences context term followed.

Lemma follow_references_det {c1 t1 t1'} (F1 : FollowReferences c1 t1 t1')
  {c2} (Ec : Map.Eq c1 c2) {t2} (Et : t1 = t2) {t2'} (F2 : FollowReferences c2 t2 t2')
  : t1' = t2'.
Proof.
  subst. rename t2 into t. generalize dependent t2'. generalize dependent c2. induction F1; intros.
  - invert F2. 2: { contradiction (N name). reflexivity. }
    apply Ec in F0. destruct (Map.find_det F F0). eapply IHF1. 2: { exact transitive. }
    eapply Map.remove_det. { exact R. } { reflexivity. } { exact Ec. } exact R0.
  - subst. invert F2. { contradiction (N name). reflexivity. } reflexivity.
Qed.

Lemma follow_references_eq {c1 t1 t1'} (F1 : FollowReferences c1 t1 t1')
  {c2} (Ec : Map.Eq c1 c2) {t2} (Et : t1 = t2) {t2'} (Et' : t1' = t2')
  : FollowReferences c2 t2 t2'.
Proof.
  subst. rename t2 into t. rename t2' into t'. generalize dependent c2. induction F1; intros.
  - econstructor. { apply Ec. exact F. } 2: { exact F1. }
    eapply Map.remove_eq. { exact R. } { reflexivity. } { exact Ec. } apply Map.eq_refl.
  - subst. constructor. { exact N. } reflexivity.
Qed.



Instance wf : Classes.WellFounded $ Telescopes.tele_measure
  (Telescopes.ext context (fun _ : context => Telescopes.tip Term.term)) nat
  (fun context (_ : Term.term) => Map.cardinality context)  lt.
Proof. apply Telescopes.wf_tele_measure. exact Subterm.lt_wf. Qed.

Equations follow_references (context : Context.context) (term : Term.term)
  : option Term.term by wf (Map.cardinality context) lt :=
  follow_references context $ Term.Var name Ownership.Referenced with Map.found_dec context name => {
  | Map.NotFound => None
  | @Map.Found next _ => follow_references (Map.remove name context) next };
  follow_references _ term := Some term.
Next Obligation.
  clear follow_references. rewrite Map.cardinality_remove. apply Map.find_iff in Y as E. rewrite E. clear E.
  unfold Map.cardinality. rewrite MapCore.cardinal_spec. apply MapCore.bindings_spec1 in Y.
  remember (MapCore.bindings context0) as b eqn:Eb; clear context0 Eb. destruct b. { invert Y. }
  cbn. apply PeanoNat.Nat.lt_succ_diag_r. Qed.
Fail Next Obligation.

Lemma follow_references_spec context term
  : Reflect.Option (FollowReferences context term) (follow_references context term).
Proof.
  funelim (follow_references context term).
  - constructor. constructor. { intros ? D. discriminate D. } reflexivity.
  - constructor. constructor. { intros ? D. discriminate D. } reflexivity.
  - constructor. constructor. { intros ? D. discriminate D. } reflexivity.
  - constructor. constructor. { intros ? D. discriminate D. } reflexivity.
  - constructor. constructor. { intros ? D. discriminate D. } reflexivity.
  - destruct H; constructor. { econstructor. { exact Y. } { apply Map.remove_remove. eexists. exact Y. } exact Y0. }
    intros t C. invert C. 2: { eapply N0. reflexivity. } eapply N. eapply follow_references_eq.
    + exact transitive.
    + eapply Map.remove_det. { exact R. } { reflexivity. } { apply Map.eq_refl. } apply Map.remove_remove. eexists. exact F.
    + eapply Map.find_det. { exact F. } exact Y.
    + reflexivity.
  - constructor. intros t C. invert C. { apply N in F as []. } eapply N0. reflexivity.
Qed.

Lemma follow_maps_to_last {context name followed} (F : FollowReferences context (Term.Var name Ownership.Referenced) followed)
  : exists second_to_last, Map.Find context second_to_last followed.
Proof.
  remember (Term.Var name Ownership.Referenced) as r eqn:Er. generalize dependent name. induction F; intros; subst.
  - symmetry in Er. invert Er. invert F0. 2: { eexists. exact F. }
    specialize (IHF _ eq_refl) as [second_to_last IH]. apply R in IH as [N IH]. eexists. exact IH.
  - edestruct N as []. reflexivity.
Qed.



From Coq Require Import String.

Definition format_pair kv : string := fst kv ++ " -> (" ++ (Term.to_string $ snd kv) ++ "); ".

Definition to_string ctx : string :=
  "{ " ++ List.fold_right String.append String.EmptyString (List.map format_pair $ MapCore.bindings ctx) ++ "}".
