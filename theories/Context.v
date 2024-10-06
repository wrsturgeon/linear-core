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



Inductive FollowReferences (context : context) symlink : String.string -> Term.term -> Prop :=
  | Immediate
      {looked_up} (lookup : Map.Find context symlink looked_up)
      (N : forall id, looked_up <> Term.Var id Ownership.Referenced)
      : FollowReferences context symlink symlink looked_up
  | Indirect
      {next} (lookup : Map.Find context symlink $ Term.Var next Ownership.Referenced)
      {without_symlink} (remove_symlink_from_context : Map.Remove symlink context without_symlink)
      {real_name looked_up} (transitive : FollowReferences without_symlink next real_name looked_up)
      : FollowReferences context symlink real_name looked_up
  .
Arguments FollowReferences context symlink real_name looked_up.

Lemma follow_references_eq {c1 n1 r1 y1} (F1 : FollowReferences c1 n1 r1 y1)
  {c2} (Ec : Map.Eq c1 c2) {n2} (En : n1 = n2) {r2} (Er : r1 = r2) {y2} (Ey : y1 = y2)
  : FollowReferences c2 n2 r2 y2.
Proof.
  subst. rename n2 into n. rename r2 into r. rename y2 into y. generalize dependent c2.
  induction F1; intros; cbn in *. { left. { apply Ec. exact lookup. } exact N. }
  eright. { apply Ec. exact lookup. } { eapply Map.remove_eq; try eassumption. { reflexivity. } apply Map.eq_refl. }
  apply IHF1. eapply Map.remove_det. { eassumption. } 3: { eassumption. } { reflexivity. } apply Map.eq_refl.
Qed.

Lemma follow_references_det {c1 n1 r1 y1} (F1 : FollowReferences c1 n1 r1 y1)
  {c2} (Ec : Map.Eq c1 c2) {n2} (En : n1 = n2) {r2 y2} (F2 : FollowReferences c2 n2 r2 y2)
  : r1 = r2 /\ y1 = y2.
Proof.
  subst. rename n2 into n. generalize dependent y2. generalize dependent r2. generalize dependent c2. induction F1; intros.
  - invert F2; apply Ec in lookup0; destruct (Map.find_det lookup0 lookup); [split | edestruct N]; reflexivity.
  - invert F2; apply Ec in lookup0. { destruct (Map.find_det lookup lookup0). edestruct N. reflexivity. }
    assert (E := Map.find_det lookup0 lookup). invert E. eapply IHF1. 2: { exact transitive. }
    eapply Map.remove_det; try eassumption. reflexivity.
Qed.

Lemma follow_references_find {c n r y} (F : FollowReferences c n r y)
  : Map.Find c r y.
Proof. cbn. induction F. { exact lookup. } apply remove_symlink_from_context in IHF as [N IH]. exact IH. Qed.



Instance wf : Classes.WellFounded $ Telescopes.tele_measure
  (Telescopes.ext context (fun _ : context => Telescopes.tip Term.term)) nat
  (fun context (_ : Term.term) => Map.cardinality context)  lt.
Proof. apply Telescopes.wf_tele_measure. exact Subterm.lt_wf. Qed.

Equations follow_references (context : Context.context) (symlink : String.string)
  : option (String.string * Term.term) by wf (Map.cardinality context) lt :=
  follow_references context symlink with Map.found_dec context symlink => {
    | Map.NotFound => None
    | @Map.Found (Term.Var next Ownership.Referenced) _ => follow_references (Map.remove symlink context) next
    | @Map.Found looked_up _ => Some (symlink, looked_up)
  }.
Next Obligation.
  clear follow_references. rewrite Map.cardinality_remove. apply Map.find_iff in Y as E. rewrite E. clear E.
  unfold Map.cardinality. rewrite MapCore.cardinal_spec. apply MapCore.bindings_spec1 in Y.
  remember (MapCore.bindings context0) as b eqn:Eb; clear context0 Eb. destruct b. { invert Y. }
  cbn. apply PeanoNat.Nat.lt_succ_diag_r. Qed.
Fail Next Obligation.

Lemma follow_references_spec context symlink
  : Reflect.Option (fun kv => FollowReferences context symlink (fst kv) $ snd kv) (follow_references context symlink).
Proof.
  funelim (follow_references context symlink); try solve [constructor; cbn; left; [exact Y |]; intros ? D; discriminate D].
  - destruct H.
    + destruct x as [k v]. cbn in *. left. cbn. eright. { exact Y. } 2: { exact Y0. }
      apply Map.remove_remove. eexists. exact Y.
    + constructor. intros [k v] C. cbn in *. invert C. { destruct (Map.find_det Y lookup). eapply N0. reflexivity. }
      apply (N (k, v)). cbn. assert (E := Map.find_det lookup Y).
      invert E. eapply follow_references_eq; try exact transitive; try reflexivity.
      eapply Map.remove_det. { exact remove_symlink_from_context. } { reflexivity. } { apply Map.eq_refl. }
      apply Map.remove_remove. eexists. exact Y.
  - constructor. intros [k v] C; cbn in *. invert C; apply N in lookup as [].
Qed.



From Coq Require Import String.

Definition format_pair kv : string := fst kv ++ " -> (" ++ (Term.to_string $ snd kv) ++ "); ".

Definition to_string ctx : string :=
  "{ " ++ List.fold_right String.append String.EmptyString (List.map format_pair $ MapCore.bindings ctx) ++ "}".
