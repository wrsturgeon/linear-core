From LinearCore Require
  BoundIn
  Context
  Term
  UsedIn
  WellFormed
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



Inductive Strict {lookup : Map.to String.string} (O2O : Map.OneToOne lookup) : Pattern.strict -> Pattern.strict -> Prop :=
  | SCtr ctor
      : Strict O2O (Pattern.Ctr ctor) (Pattern.Ctr ctor)
  | SApp
      argument renamed_argument unused (rename_argument : Map.Pop lookup argument renamed_argument unused)
      (O2OU : Map.OneToOne unused) curried renamed_curried (rename_curried : Strict O2OU curried renamed_curried)
      : Strict O2O (Pattern.App curried argument) (Pattern.App renamed_curried renamed_argument)
  .
Arguments Strict {lookup} O2O strict renamed_strict.

Lemma strict_eq
  {l1} {O2O1 : Map.OneToOne l1} {s1 r1} (S1 : Strict O2O1 s1 r1)
  {l2} (El : Map.Eq l1 l2) (O2O2 : Map.OneToOne l2)
  {s2} (Es : s1 = s2)
  {r2} (Er : r1 = r2)
  : Strict O2O2 s2 r2.
Proof.
  subst. generalize dependent l2. induction S1; intros. { constructor. }
  econstructor. { eapply Map.pop_eq; try reflexivity; try eassumption. apply Map.eq_refl. } exact S1.
Qed.

Fixpoint strict lookup s :=
  match s with
  | Pattern.Ctr ctor => Some s
  | Pattern.App curried argument =>
      match Map.pop lookup argument with None => None | Some (renamed_argument, unused) =>
        match strict unused curried with None => None | Some renamed_curried =>
          Some (Pattern.App renamed_curried renamed_argument)
        end
      end
  end.

Lemma strict_spec {lookup} (O2O : Map.OneToOne lookup) s
  : Reflect.Option (Strict O2O s) (strict lookup s).
Proof.
  generalize dependent lookup. induction s; intros; cbn in *. { constructor. constructor. }
  fold (Map.pop lookup argument). destruct (Map.pop_spec lookup argument) as [[renamed_argument unused] |]. 2: {
    constructor. intros p S. invert S. apply (N (_, _)) in rename_argument as []. } simpl fst in *. simpl snd in *.
  assert (O2OU : Map.OneToOne unused). { eapply Map.one_to_one_remove_if_present. { exact O2O. } apply Y. }
  specialize (IHs _ O2OU). destruct IHs; constructor. { econstructor. { exact Y. } exact Y0. }
  intros p C. invert C. eapply N. eapply strict_eq; try reflexivity. { exact rename_curried. }
  eapply Map.pop_det; try reflexivity; try eassumption. apply Map.eq_refl.
Qed.

Lemma strict_det
  {l1} {O2O1 : Map.OneToOne l1} {s1 r1} (S1 : Strict O2O1 s1 r1)
  {l2} (El : Map.Eq l1 l2) (O2O2 : Map.OneToOne l2)
  {s2} (Es : s1 = s2)
  {r2} (S2 : Strict O2O2 s2 r2)
  : r1 = r2.
Proof.
  subst. generalize dependent r2. generalize dependent l2.
  induction S1; intros; invert S2. { reflexivity. }
  destruct (Map.pop_det rename_argument El eq_refl rename_argument0) as [<- Eu].
  f_equal. eapply IHS1. { exact Eu. } exact rename_curried.
Qed.

Definition CompatibleStrict (lookup : Map.to String.string) strict : Prop :=
  Map.OneToOne lookup /\
  WellFormed.Strict strict /\
  Map.Subset (BoundIn.strict strict) (Map.domain lookup).

Lemma compatible_if_strict {lookup} {O2O : Map.OneToOne lookup} {strict renamed_strict} (S : Strict O2O strict renamed_strict)
  : CompatibleStrict lookup strict.
Proof.
  induction S. { split. { exact O2O. } split. { constructor. } intros k v F. invert F. }
  destruct IHS as [O2OU' [WF SS]]. split. { exact O2O. } split.
  - constructor. { exact WF. } intro B. apply BoundIn.strict_iff in B as [[] B]. apply SS in B.
    apply Map.find_domain in B as [name B]. apply rename_argument in B as [N _]. apply N. reflexivity.
  - intros k v F. apply Map.find_domain. cbn in F. apply Map.find_overriding_add in F as [[-> ->] | [N F]].
    + destruct rename_argument as [F R]. eexists. exact F.
    + apply SS in F. apply Map.find_domain in F as [name F]. apply rename_argument in F as [Nk F]. eexists. exact F.
Qed.

Lemma strict_iff_compatible lookup strict
  : CompatibleStrict lookup strict <->
    exists (O2O : Map.OneToOne lookup) renamed_strict,
    Strict O2O strict renamed_strict.
Proof.
  generalize dependent lookup. induction strict; intros.
  - split. { intros [O2O [WF S]]. exists O2O. eexists. constructor. }
    intros [O2O [renamed_strict S]]. split. { exact O2O. } split. { constructor. } intros k v F. invert F.
  - split. 2: { intros [O2O [renamed_strict S]]. eapply compatible_if_strict. exact S. }
    intros [O2O [WF S]]. invert WF. assert (A := S). eapply Map.find_domain in A as [renamed_argument A]. 2: {
      apply Map.find_overriding_add. left. split; reflexivity. }
    assert (C : CompatibleStrict (Map.remove argument lookup) strict0). {
      split. { eapply Map.one_to_one_remove_if_present. 2: { apply Map.remove_if_present_remove. } exact O2O. }
      split. { exact curried_well_formed. } intros k v F. apply Map.find_domain.
      eapply Map.in_remove_if_present. { apply Map.remove_if_present_remove. }
      assert (Nk : k <> argument). { intros ->. apply N. apply BoundIn.strict_iff. eexists. exact F. }
      split. { exact Nk. } eapply Map.find_domain. apply S. cbn. apply Map.find_overriding_add.
      right. split. { exact Nk. } exact F. }
    apply IHstrict in C as [O2OR [renamed_strict C]]. exists O2O. eexists. econstructor. 2: { exact C. }
    split. { exact A. } apply Map.remove_if_present_remove.
Qed.

Lemma strict_reversible {lookup} {O2O : Map.OneToOne lookup} {inverted} (inv : Map.Invert lookup inverted)
  (O2OI : Map.OneToOne inverted) strict renamed_strict
  : Strict O2O strict renamed_strict <-> Strict O2OI renamed_strict strict.
Proof. { split; intro S.
  - generalize dependent inverted. induction S; intros; econstructor.
    + destruct rename_argument as [F R]. split. { apply inv. exact F. } apply Map.remove_if_present_remove.
    + apply IHS. intros k v. assert (A := @Map.remove_if_present_remove); cbn in A; rewrite A; clear A.
      destruct rename_argument as [F R]. cbn in R. rewrite R. split; (intros [N F']; split; [| apply inv; exact F']).
      * intros ->. apply N. eapply O2O; eassumption.
      * intros ->. apply N. apply inv in F'. eapply Map.find_det; eassumption.
  - generalize dependent lookup. induction S; intros; econstructor.
    + destruct rename_argument as [F R]. split. { apply inv. exact F. } apply Map.remove_if_present_remove.
    + apply IHS. intros k v. assert (A := @Map.remove_if_present_remove); cbn in A; rewrite A; clear A.
      destruct rename_argument as [F R]. cbn in R. rewrite R. split; (intros [N F']; split; [| apply inv; exact F']).
      * intros ->. apply N. apply inv in F'. eapply Map.find_det; eassumption.
      * intros ->. apply N. eapply O2O; eassumption. }
  Unshelve.
  - eapply Map.one_to_one_remove_if_present. 2: { apply Map.remove_if_present_remove. } exact O2OI.
  - eapply Map.one_to_one_remove_if_present. 2: { apply Map.remove_if_present_remove. } exact O2O0.
Qed.

Lemma bound_in_strict {lookup} {O2O : Map.OneToOne lookup}
  {strict renamed_strict} (R : Strict O2O strict renamed_strict) y
  : BoundIn.Strict renamed_strict y <-> exists x, (BoundIn.Strict strict x /\ Map.Find lookup x y).
Proof.
  generalize dependent y. induction R; intros. { split. { intro B. invert B. } intros [x [B F]]. invert B. } split.
  - intro B. invert B.
    + destruct rename_argument as [F RIP]. eexists. split. { left. } exact F.
    + apply IHR in bound_earlier as [x [B F]]. eexists. split. { right. exact B. }
      apply rename_argument in F as [N F]. exact F.
  - intros [x [B F]]. destruct rename_argument as [Fu Ru].
    destruct (String.eqb_spec x argument). { subst. destruct (Map.find_det Fu F). left. }
    invert B. { contradiction n. reflexivity. } right. apply IHR. eexists.
    split. { exact bound_earlier. } apply Ru. split. { exact n. } exact F.
Qed.

Lemma wf_strict {lookup} {O2O : Map.OneToOne lookup} {strict renamed_strict} (R : Strict O2O strict renamed_strict)
  : WellFormed.Strict renamed_strict.
Proof.
  induction R; constructor. { exact IHR. } intro B. destruct (compatible_if_strict R) as [O2O' [WF S]].
  apply (bound_in_strict R) in B as [cant_exist [B F]]. destruct rename_argument as [F' R']. apply R' in F as [N F].
  apply N. eapply O2O. { exact F. } exact F'.
Qed.



Variant MoveOrReference {lookup} (O2O : Map.OneToOne lookup) : Pattern.move_or_reference -> Pattern.move_or_reference -> Prop :=
  | MMov strict renamed_strict (rename_strict : Strict O2O strict renamed_strict)
      : MoveOrReference O2O (Pattern.Mov strict) (Pattern.Mov renamed_strict)
  | MRef strict renamed_strict (rename_strict : Strict O2O strict renamed_strict)
      : MoveOrReference O2O (Pattern.Ref strict) (Pattern.Ref renamed_strict)
  .
Arguments MoveOrReference {lookup} O2O pattern renamed_pattern.

Definition move_or_reference lookup mr :=
  match mr with
  | Pattern.Mov s => option_map Pattern.Mov (strict lookup s)
  | Pattern.Ref s => option_map Pattern.Ref (strict lookup s)
  end.

Lemma move_or_reference_spec {lookup} (O2O : Map.OneToOne lookup) mr
  : Reflect.Option (MoveOrReference O2O mr) (move_or_reference lookup mr).
Proof.
  destruct mr; cbn; (destruct (strict_spec O2O strict0); constructor; [constructor; exact Y |]);
  intros s M; invert M; apply N in rename_strict as [].
Qed.

Lemma move_or_reference_det
  {l1} {O2O1 : Map.OneToOne l1} {mr1 r1} (MR1 : MoveOrReference O2O1 mr1 r1)
  {l2} (El : Map.Eq l1 l2) (O2O2 : Map.OneToOne l2)
  {mr2} (Emr : mr1 = mr2)
  {r2} (MR2 : MoveOrReference O2O2 mr2 r2)
  : r1 = r2.
Proof. invert MR1; invert MR2; f_equal; eapply strict_det; try reflexivity; eassumption. Qed.

Lemma move_or_reference_eq
  {l1} {O2O1 : Map.OneToOne l1} {mr1 r1} (MR1 : MoveOrReference O2O1 mr1 r1)
  {l2} (El : Map.Eq l1 l2) (O2O2 : Map.OneToOne l2)
  {mr2} (Emr : mr1 = mr2)
  {r2} (Er : r1 = r2)
  : MoveOrReference O2O2 mr2 r2.
Proof. subst. invert MR1; constructor; eapply strict_eq; try reflexivity; eassumption. Qed.

Variant CompatibleMoveOrReference lookup : Pattern.move_or_reference -> Prop :=
  | CMov strict (CS : CompatibleStrict lookup strict)
      : CompatibleMoveOrReference lookup (Pattern.Mov strict)
  | CRef strict (CS : CompatibleStrict lookup strict)
      : CompatibleMoveOrReference lookup (Pattern.Ref strict)
  .

Lemma move_or_reference_iff_compatible lookup move_or_reference
  : CompatibleMoveOrReference lookup move_or_reference <->
    exists (O2O : Map.OneToOne lookup) renamed_move_or_reference,
    MoveOrReference O2O move_or_reference renamed_move_or_reference.
Proof.
  split.
  - intro C. invert C; apply strict_iff_compatible in CS as [O2O [renamed_strict S]]; exists O2O; eexists; constructor; exact S.
  - intros [O2O [renamed_move_or_reference MR]].
    invert MR; constructor; apply strict_iff_compatible; exists O2O; eexists; exact rename_strict.
Qed.

Lemma move_or_reference_reversible {lookup} (O2O : Map.OneToOne lookup) {inverted} (inv : Map.Invert lookup inverted)
  (O2OI : Map.OneToOne inverted) move_or_reference renamed_move_or_reference
  : MoveOrReference O2O move_or_reference renamed_move_or_reference <-> MoveOrReference O2OI renamed_move_or_reference move_or_reference.
Proof. split; intro MR; invert MR; constructor; eapply strict_reversible; try eassumption; apply Map.invert_sym; assumption. Qed.

Lemma bound_in_move_or_reference {lookup} {O2O : Map.OneToOne lookup}
  {move_or_reference renamed_move_or_reference} (R : MoveOrReference O2O move_or_reference renamed_move_or_reference) y
  : BoundIn.MoveOrReference renamed_move_or_reference y <-> exists x, (BoundIn.MoveOrReference move_or_reference x /\ Map.Find lookup x y).
Proof.
  split.
  - intro B. invert B; invert R; (eapply bound_in_strict in bound_in_strict0 as [x [B F]]; [| eassumption]);
    eexists; (split; [| exact F]); constructor; exact B.
  - intros [x [B F]]. invert B; invert R; constructor; (eapply bound_in_strict; [eassumption |]); eexists; split; eassumption.
Qed.



Variant Pattern {lookup} (O2O : Map.OneToOne lookup) : Pattern.pattern -> Pattern.pattern -> Prop :=
  | Nam name renamed (rename_name : Map.Find lookup name renamed)
      : Pattern O2O (Pattern.Nam name) (Pattern.Nam renamed)
  | Pat move_or_reference renamed_move_or_reference
      (rename_move_or_reference : MoveOrReference O2O move_or_reference renamed_move_or_reference)
      : Pattern O2O (Pattern.Pat move_or_reference) (Pattern.Pat renamed_move_or_reference)
  .
Arguments Pattern {lookup} O2O pattern renamed_pattern.

Definition pattern lookup patt :=
  match patt with
  | Pattern.Nam name => option_map Pattern.Nam (Map.find lookup name)
  | Pattern.Pat mr => option_map Pattern.Pat (move_or_reference lookup mr)
  end.

Lemma pattern_spec {lookup} (O2O : Map.OneToOne lookup) patt
  : Reflect.Option (Pattern O2O patt) (pattern lookup patt).
Proof.
  destruct patt; cbn in *.
  - destruct (Map.find_spec lookup name); constructor. { constructor. exact Y. }
    intros p P. invert P. apply N in rename_name as [].
  - destruct (move_or_reference_spec O2O move_or_reference0); constructor. { constructor. exact Y. }
    intros p P. invert P. apply N in rename_move_or_reference as [].
Qed.

Lemma pattern_det
  {l1} {O2O1 : Map.OneToOne l1} {p1 r1} (P1 : Pattern O2O1 p1 r1)
  {l2} (El : Map.Eq l1 l2) (O2O2 : Map.OneToOne l2)
  {p2} (Ep : p1 = p2)
  {r2} (P2 : Pattern O2O2 p2 r2)
  : r1 = r2.
Proof.
  invert P1; invert P2; f_equal. { eapply Map.find_det. { eassumption. } apply El. assumption. }
  eapply move_or_reference_det; try reflexivity; eassumption.
Qed.

Lemma pattern_eq
  {l1} {O2O1 : Map.OneToOne l1} {p1 r1} (P1 : Pattern O2O1 p1 r1)
  {l2} (El : Map.Eq l1 l2) (O2O2 : Map.OneToOne l2)
  {p2} (Ep : p1 = p2)
  {r2} (Er : r1 = r2)
  : Pattern O2O2 p2 r2.
Proof.
  subst. invert P1; constructor. { apply El. exact rename_name. }
  eapply move_or_reference_eq; try reflexivity; eassumption.
Qed.

Lemma pattern_iff {lookup} (O2O : Map.OneToOne lookup) patt renamed_patt
  : Pattern O2O patt renamed_patt <-> pattern lookup patt = Some renamed_patt.
Proof.
  destruct (pattern_spec O2O patt).
  - split. 2: { intro E. invert E. exact Y. }
    intro P. f_equal. eapply pattern_det; try reflexivity; try eassumption. apply Map.eq_refl.
  - split. { intro P. apply N in P as []. } intro D. discriminate D.
Qed.

Variant CompatiblePattern lookup : Pattern.pattern -> Prop :=
  | CNam (O2O : Map.OneToOne lookup) name (I : Map.In lookup name)
      : CompatiblePattern lookup (Pattern.Nam name)
  | CPat move_or_reference (C : CompatibleMoveOrReference lookup move_or_reference)
      : CompatiblePattern lookup (Pattern.Pat move_or_reference)
  .

Lemma pattern_iff_compatible lookup pattern
  : CompatiblePattern lookup pattern <->
    exists (O2O : Map.OneToOne lookup) renamed_pattern, Pattern O2O pattern renamed_pattern.
Proof.
  split.
  - intro CP. invert CP.
    + exists O2O. destruct I as [y F]. eexists. constructor. exact F.
    + apply move_or_reference_iff_compatible in C as [O2O [renamed_move_or_reference C]].
      exists O2O. eexists. constructor. exact C.
  - intros [O2O [renamed_pattern P]]. invert P. { constructor. { exact O2O. } eexists. exact rename_name. }
    constructor. apply move_or_reference_iff_compatible. exists O2O. eexists. exact rename_move_or_reference.
Qed.

Lemma pattern_reversible {lookup} (O2O : Map.OneToOne lookup) {inverted} (inv : Map.Invert lookup inverted)
  (O2OI : Map.OneToOne inverted) pattern renamed_pattern
  : Pattern O2O pattern renamed_pattern <-> Pattern O2OI renamed_pattern pattern.
Proof.
  split; intro P.
  - generalize dependent inverted. induction P; intros. { constructor. apply inv. exact rename_name. }
    constructor. eapply move_or_reference_reversible. { apply Map.invert_sym. eassumption. } eassumption.
  - generalize dependent lookup. induction P; intros. { constructor. apply inv. exact rename_name. }
    constructor. eapply move_or_reference_reversible; eassumption.
Qed.

Lemma bound_in_pattern {lookup} {O2O : Map.OneToOne lookup}
  {pattern renamed_pattern} (R : Pattern O2O pattern renamed_pattern) y
  : BoundIn.Pattern renamed_pattern y <-> exists x, (BoundIn.Pattern pattern x /\ Map.Find lookup x y).
Proof.
  invert R.
  + split. { intro B. invert B. eexists. split. { constructor. } exact rename_name. }
    intros [x [B F]]. invert B. destruct (Map.find_det rename_name F). constructor.
  + split.
    * intro B. invert B. eapply bound_in_move_or_reference in bound_in_move_or_reference0 as [x [B F]]. 2: { eassumption. }
      eexists. split. { constructor. exact B. } exact F.
    * intros [x [B F]]. invert B. constructor. eapply bound_in_move_or_reference. { eassumption. }
      eexists. split; eassumption.
Qed.



Lemma strict_nodes_left_eq {lookup p r} (E : strict lookup p = Some r)
  : Pattern.strict_nodes_left r = Pattern.strict_nodes_left p.
Proof.
  generalize dependent r. generalize dependent lookup. induction p; intros; cbn in *. { invert E. reflexivity. }
  destruct Map.find; cbn in *. 2: { discriminate E. } destruct strict eqn:E'; invert E. cbn. f_equal. eapply IHp. exact E'.
Qed.

Lemma strict_nodes_eq {lookup p r} (E : strict lookup p = Some r)
  : Pattern.strict_nodes r = Pattern.strict_nodes p.
Proof.
  generalize dependent r. generalize dependent lookup. induction p; intros; cbn in *. { invert E. reflexivity. }
  destruct Map.find; cbn in *. 2: { discriminate E. } destruct strict eqn:E'; invert E. cbn. do 2 f_equal. eapply IHp. exact E'.
Qed.

Lemma move_or_reference_nodes_eq {lookup p r} (E : move_or_reference lookup p = Some r)
  : Pattern.move_or_reference_nodes r = Pattern.move_or_reference_nodes p.
Proof. destruct p; cbn in *; destruct strict eqn:E'; invert E; eapply strict_nodes_eq; exact E'. Qed.

Lemma pattern_nodes_eq {lookup p r} (E : pattern lookup p = Some r)
  : Pattern.nodes r = Pattern.nodes p.
Proof.
  destruct p; cbn in *. { destruct Map.find; invert E. reflexivity. }
  destruct move_or_reference eqn:E'; invert E. cbn. eapply move_or_reference_nodes_eq. exact E'.
Qed.
