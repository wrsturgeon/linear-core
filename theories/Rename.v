From LinearCore Require
  BoundIn
  Context
  Name
  Term
  UsedIn
  WellFormed
  .
From LinearCore Require Import
  Invert
  .



Inductive Strict {lookup : Map.to Name.name} (O2O : Map.OneToOne lookup) : Pattern.strict -> Pattern.strict -> Prop :=
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

Definition CompatibleStrict (lookup : Map.to Name.name) strict : Prop :=
  Map.OneToOne lookup /\
  WellFormed.Strict strict /\
  Map.Subset (BoundIn.strict strict) (Map.domain lookup).

Lemma compatible_if_strict {lookup} {O2O : Map.OneToOne lookup} {strict renamed_strict} (S : Strict O2O strict renamed_strict)
  : CompatibleStrict lookup strict.
Proof.
  induction S. { split. { exact O2O. } split. { constructor. } intros k v F. invert F. }
  destruct IHS as [O2OU' [WF SS]]. split. { exact O2O. } split.
  - constructor. { exact WF. } intro B. apply BoundIn.strict_spec in B as [[] B]. apply SS in B.
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
      assert (Nk : k <> argument). { intros ->. apply N. apply BoundIn.strict_spec. eexists. exact F. }
      split. { exact Nk. } eapply Map.find_domain. apply S. cbn. apply Map.find_overriding_add.
      right. split. { exact Nk. } exact F. }
    apply IHstrict in C as [O2OR [renamed_strict C]]. exists O2O. eexists. econstructor. 2: { exact C. }
    split. { exact A. } apply Map.remove_if_present_remove.
Qed.

Lemma strict_reversible {lookup} (O2O : Map.OneToOne lookup) {inverted} (inv : Map.Invert lookup inverted)
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



Inductive Term {lookup : Map.to Name.name} (O2O : Map.OneToOne lookup) : Term.term -> Term.term -> Prop :=
  | Ctr ctor
      : Term O2O (Term.Ctr ctor) (Term.Ctr ctor) (* constructor names live in a different universe *)
  | Mov x y (F : Map.Find lookup x y)
      : Term O2O (Term.Mov x) (Term.Mov y)
  | Ref x y (F : Map.Find lookup x y)
      : Term O2O (Term.Ref x) (Term.Ref y)
  | App
      function renamed_function (function_renaming : Term O2O function renamed_function)
      argument renamed_argument (argument_renaming : Term O2O argument renamed_argument)
      : Term O2O (Term.App function argument) (Term.App renamed_function renamed_argument)
  | For
      type renamed_type (type_renaming : Term O2O type renamed_type)
      variable variable_only (only_variable : Map.Singleton variable tt variable_only)
      unshadowed (not_shadowed : Map.OverwriteIfPresent variable variable lookup unshadowed)
      {O2OU : Map.OneToOne unshadowed} body renamed_body (body_renaming : Term O2OU body renamed_body)
      : Term O2O (Term.For variable type body) (Term.For variable renamed_type renamed_body)
  | Cas
      other_cases renamed_other_cases (other_cases_renaming : Term O2O other_cases renamed_other_cases)
      pattern bound_in_pattern (find_pattern_bindings : Map.Reflect (BoundIn.Pattern pattern) bound_in_pattern)
      pattern_to_self (pattern_idem : Map.ToSelf bound_in_pattern pattern_to_self)
      unshadowed (not_shadowed : Map.BulkOverwrite pattern_to_self lookup unshadowed) {O2OU : Map.OneToOne unshadowed}
      body_if_match renamed_body_if_match (body_if_match_renaming : Term O2OU body_if_match renamed_body_if_match)
      : Term O2O
        (Term.Cas pattern body_if_match other_cases)
        (Term.Cas pattern renamed_body_if_match renamed_other_cases)
  .
Arguments Term {lookup} O2O term renamed.



Lemma term_eq {l1} {O2O1 : Map.OneToOne l1} {t1 y1} (R1 : Term O2O1 t1 y1)
  {l2} (El : Map.Eq l1 l2) (O2O2 : Map.OneToOne l2)
  {t2} (Et : t1 = t2)
  {y2} (Ey : y1 = y2)
  : Term O2O2 t2 y2.
Proof.
  subst. rename t2 into t. rename y2 into y. generalize dependent l2.
  induction R1; intros; try solve [constructor; apply El; exact F].
  - constructor; [apply IHR1_1 | apply IHR1_2]; exact El.
  - econstructor; try eassumption. { apply IHR1_1. exact El. }
    intros k v. cbn in not_shadowed. rewrite not_shadowed. cbn in El. rewrite El. reflexivity.
  - econstructor; try eassumption. { apply IHR1_1. exact El. }
    intros k v. cbn in not_shadowed. rewrite not_shadowed. cbn in El. rewrite El. reflexivity.
Qed.

Lemma term_det {l1} {O2O1 : Map.OneToOne l1} {t1 y1} (R1 : Term O2O1 t1 y1)
  {l2} (El : Map.Eq l1 l2) (O2O2 : Map.OneToOne l2)
  {t2} (Et : t1 = t2)
  {y2} (R2 : Term O2O2 t2 y2)
  : y1 = y2.
Proof.
  subst. rename t2 into t. generalize dependent y2. generalize dependent l2.
  induction R1; intros; try solve [invert R2; reflexivity].
  - invert R2. f_equal. apply El in F0. eapply Map.find_det; eassumption.
  - invert R2. f_equal. apply El in F0. eapply Map.find_det; eassumption.
  - invert R2. f_equal; [eapply IHR1_1 | eapply IHR1_2]; eassumption.
  - invert R2. f_equal; [eapply IHR1_1 | eapply IHR1_2]; try eassumption.
    eapply Map.overwrite_if_present_det; try reflexivity; eassumption.
  - invert R2. f_equal; [eapply IHR1_2 | eapply IHR1_1]; try eassumption.
    eapply Map.bulk_overwrite_det; try reflexivity; try eassumption.
    eapply Map.to_self_det; try eassumption.
    intros k []; split; intro F; (eassert (I : (Map.In _ _)); [eexists; exact F |]);
    [apply find_pattern_bindings in I | apply find_pattern_bindings0 in I];
    [apply find_pattern_bindings0 in I | apply find_pattern_bindings in I];
    destruct I as [[] F']; exact F'.
Qed.

Lemma term_superset {lil} {O2Ol : Map.OneToOne lil} {tl yl} (Rl : Term O2Ol tl yl)
  {big} (S : Map.Subset lil big) (O2Ob : Map.OneToOne big)
  (caveat : forall x (B : BoundIn.Term tl x) z (F : Map.Find big z x), z = x)
  {tb} (Et : tl = tb)
  {yb} (Ey : yl = yb)
  : Term O2Ob tb yb.
Proof.
  subst. rename tb into t. rename yb into y. generalize dependent big. {
  induction Rl; intros; try solve [constructor; apply S; exact F].
  - constructor; [eapply IHRl1 | eapply IHRl2]; try exact S; intros;
    (apply caveat; [| exact F]); [apply BoundIn.TApF | apply BoundIn.TApA]; exact B.
  - econstructor. { apply IHRl1; intros. { exact S. } apply caveat. 2: { exact F. } apply BoundIn.TFoT. exact B. }
    { exact only_variable. } { apply Map.overwrite_if_present_overwrite. } apply IHRl2. 2: {
      intros. apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]. { reflexivity. }
      apply caveat. 2: { exact F. } apply BoundIn.TFoB. exact B. }
    intros k v. cbn in not_shadowed. rewrite not_shadowed.
    assert (A := @Map.overwrite_if_present_overwrite); cbn in A; rewrite A; clear A.
    intros [[-> ->] | [N F]]; [left | right]; [split; reflexivity |]. split. { exact N. } apply S. exact F.
  - econstructor. { apply IHRl1; intros. { exact S. } apply caveat. 2: { exact F. } apply BoundIn.TCaO. exact B. }
    { eassumption. } { eassumption. } { apply Map.bulk_overwrite_bulk_overwrite. } apply IHRl2. 2: {
      intros. apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]].
      + apply pattern_idem in F as [I ->]. reflexivity.
      + apply caveat. 2: { exact F. } apply BoundIn.TCaB. exact B. }
    intros k v. cbn in not_shadowed. rewrite not_shadowed.
    assert (A := @Map.bulk_overwrite_bulk_overwrite); cbn in A; rewrite A; clear A.
    intros [F | [N F]]; [left; exact F | right]. split. { exact N. } apply S. exact F. }
  Unshelve.
  - eapply Map.one_to_one_overwrite. { apply Map.overwrite_if_present_overwrite. }
    split; intros. { eapply O2Ob; eassumption. } apply caveat. { constructor. } exact F.
  - eapply Map.one_to_one_bulk_overwrite. { apply Map.bulk_overwrite_bulk_overwrite. }
    split. { cbn. intros. apply pattern_idem in F1 as [I1 ->]. apply pattern_idem in F2 as [I2 ->]. reflexivity. }
    split; intros. { eapply O2Ob; eassumption. } apply pattern_idem in Ff as [If ->].
    apply caveat. 2: { exact Fo. } apply BoundIn.TCaP. apply find_pattern_bindings. exact If.
Qed.

Lemma term_then_in_domain {lookup} {O2O : Map.OneToOne lookup} {term renamed_term} (T : Term O2O term renamed_term)
  {x} (U : UsedIn.Term term x)
  : Map.In lookup x.
Proof.
  generalize dependent x. induction T; intros; invert U.
  - eexists. exact F.
  - eexists. exact F.
  - apply IHT1. exact used_in_function.
  - apply IHT2. exact used_in_argument.
  - apply IHT1. exact used_in_type.
  - apply IHT2 in used_in_body as [y F]. apply not_shadowed in F as [[-> ->] | [N F]].
    + contradiction not_shadowed0. reflexivity.
    + eexists. exact F.
  - apply IHT2 in used_in_body as [y F]. apply not_shadowed in F as [F | [N F]].
    + contradiction not_shadowed0. apply find_pattern_bindings. apply pattern_idem in F as [I ->]. exact I.
    + eexists. exact F.
  - apply IHT1. exact used_in_another_case.
Qed.

Lemma term_then_in_range {lookup} {O2O : Map.OneToOne lookup} {term renamed_term} (T : Term O2O term renamed_term)
  {x} (U : UsedIn.Term renamed_term x)
  : Map.InRange lookup x.
Proof.
  generalize dependent x. induction T; intros; invert U.
  - eexists. exact F.
  - eexists. exact F.
  - apply IHT1. exact used_in_function.
  - apply IHT2. exact used_in_argument.
  - apply IHT1. exact used_in_type.
  - apply IHT2 in used_in_body as [y F]. apply not_shadowed in F as [[-> ->] | [N F]].
    + contradiction not_shadowed0. reflexivity.
    + eexists. exact F.
  - apply IHT2 in used_in_body as [y F]. apply not_shadowed in F as [F | [N F]].
    + contradiction not_shadowed0. apply find_pattern_bindings. apply pattern_idem in F as [I ->]. exact I.
    + eexists. exact F.
  - apply IHT1. exact used_in_another_case.
Qed.

(*
Lemma term_reversible_bwd {lookup} (O2O : Map.OneToOne lookup) {term renamed_term} (fwd : Term O2O term renamed_term)
  : exists undo (O2OU : Map.OneToOne undo), (
      Term O2OU renamed_term term /\
      (forall x, Map.In undo x <-> UsedIn.Term renamed_term x)
    ).
Proof.
  induction fwd; try solve [exists Map.empty; exists Map.one_to_one_empty; split; intros; [constructor |];
    split; [intro I; apply Map.empty_empty in I as [] | intro U; invert U]].
  - eexists. eexists (Map.one_to_one_singleton _ _). split; intros. { constructor. apply Map.find_singleton. split; reflexivity. }
    split. { intro I. apply Map.in_singleton in I as ->. constructor. } intro U. invert U. apply Map.in_singleton. reflexivity.
  - eexists. eexists (Map.one_to_one_singleton _ _). split; intros. { constructor. apply Map.find_singleton. split; reflexivity. }
    split. { intro I. apply Map.in_singleton in I as ->. constructor. } intro U. invert U. apply Map.in_singleton. reflexivity.
  - destruct IHfwd1 as [mf [Of [Rf Df]]]. destruct IHfwd2 as [ma [Oa [Ra Da]]].
    exists (Map.overriding_union mf ma). eexists. split.
    + constructor; (eapply term_superset; try reflexivity; try eassumption).
      * cbn. intros. eapply Map.union_overriding. 2: { left. exact F. } cbn. intros.
        assert (Uf : UsedIn.Term renamed_function k0). { apply Df. eexists. exact F0. }
        assert (Ua : UsedIn.Term renamed_argument k0). { apply Da. eexists. exact F1. }
        (* I think this could have been bound way above so it's not an absurd case--we just need to ensure cross-branch consistency *)



  split; intro T.
  - generalize dependent inverted. induction T; intros; try solve [constructor; apply inv; exact F].
    + constructor; [apply IHT1 | apply IHT2]; exact inv.
    + econstructor. { apply IHT1. exact inv. } { eassumption. } { apply Map.overwrite_if_present_overwrite. }
      Unshelve. 2: { eapply Map.one_to_one_overwrite. { apply Map.overwrite_if_present_overwrite. } split; intros.
      * apply inv in F1. apply inv in F2. eapply Map.find_det; eassumption.
      * apply inv in F.
      eapply IHT2.



      asdf.
      apply IHT2. intros k v. cbn in not_shadowed; rewrite not_shadowed.
      assert (A := @Map.overwrite_if_present_overwrite); cbn in A; rewrite A; clear A. cbn in inv; rewrite <- inv.
      split; (intros [[-> ->] | [N F]]; [left; split; reflexivity | right]); (split; [| exact F]); intros ->.
      * apply N. eapply O2OU; apply not_shadowed. 2: { left. split; reflexivity. } right. split; assumption.
      * assert (copy := O2OU). eapply Map.one_to_one_overwrite in copy as [D E]. 2: { exact not_shadowed. }
        apply N in E as [].

        assert (A : Map.Find unshadowed variable v). { apply not_shadowed. left.
Qed.

Lemma term_reversible {lookup} (O2O : Map.OneToOne lookup) term renamed_term
  : Term O2O term renamed_term <-> exists undo (O2OU : Map.OneToOne undo), Term O2OU renamed_term term.
*)



(*
(* TODO: Grammar: should this have an `e`? I'm leaning toward yes. *)
Definition RenameableTerm (lookup : Map.to Name.name) term : Prop :=
  Map.OneToOne lookup /\
  (forall v (B : BoundIn.Term term v) k (F : Map.Find lookup k v), k = v) /\ (* can't rename an unbound variable into a bound one *)
  forall x (U : UsedIn.Term term x), Map.In lookup x.
Arguments RenameableTerm lookup term/.

Lemma renameable_term lookup term
  : (exists (O2O : Map.OneToOne lookup) renamed, Term O2O term renamed) <-> RenameableTerm lookup term.
Proof.
  cbn. split.
  - intros [O2O [renamed R]]; intros. split. { exact O2O. }
    induction R; intros; try solve [split; intros; [invert B | invert U]].
    + split; intros.
      * invert B.
      * invert U. eexists. exact F.
    + split; intros.
      * invert B.
      * invert U. eexists. exact F.
    + split; intros.
      * invert B; [eapply IHR1 | eapply IHR2]; eassumption.
      * invert U; [apply IHR1 | apply IHR2]; assumption.
    + split; intros.
      * invert B.
        -- eapply O2OU; apply not_shadowed. 2: { left. split; reflexivity. }
           destruct (Name.spec k v); [left | right]. { subst. split; reflexivity. }
           split. { exact N. } exact F.
        -- apply IHR1. { exact bound_in_type. } exact F.
        -- destruct (Name.spec k variable). 2: { apply IHR2. { exact bound_in_body. }
             apply not_shadowed. right. split. { exact N. } exact F. }
           subst.
           (* Definition is not precise enough: we can't map *to* a term that's bound
            * ... *UNLESS* what it's bound *from* is bound *first*,
            * in which case it's kicked out of the mappings before it's a problem.
            * But writing that down is just as hard as trying the actual thing. *)
Qed.
*)



(* The above complication--that the exact conditions determining whether a term is renameable is just as complex as renaming them--
 * means that we can't have bidirectional implication, but being slightly too cautious makes the permissive case easy to prove: *)
Definition ExtraSafe (lookup : Map.to Name.name) term : Prop :=
  Map.OneToOne lookup /\
  (forall v (B : BoundIn.Term term v) k (F : Map.Find lookup k v), k = v) /\ (* can't rename an unbound variable into a bound one *)
  forall x (U : UsedIn.Term term x), Map.In lookup x.

(* TODO: Grammar: should this have an `e`? I'm leaning toward yes. *)
Lemma renameable lookup term (safe : ExtraSafe lookup term)
  : exists (O2O : Map.OneToOne lookup) renamed_term, Term O2O term renamed_term.
Proof.
  destruct safe as [O2O [no_capture covering]]. exists O2O. { generalize dependent lookup.
  induction term; intros; try solve [eexists; constructor].
  - edestruct covering as [y F]. { constructor. } eexists. constructor. exact F.
  - edestruct covering as [y F]. { constructor. } eexists. constructor. exact F.
  - edestruct IHterm1; [| | edestruct IHterm2; [| | eexists; constructor; eassumption]]; intros.
    + apply no_capture. { apply BoundIn.TApF. exact B. } exact F.
    + apply covering. apply UsedIn.ApF. exact U.
    + apply no_capture. { apply BoundIn.TApA. exact B. } exact F.
    + apply covering. apply UsedIn.ApA. exact U.
  - edestruct IHterm1; [| | edestruct IHterm2; [| | eexists; econstructor; try eassumption]]; intros.
    5: { apply Map.singleton_singleton. } 5: { apply Map.overwrite_if_present_overwrite. }
    + apply no_capture. { apply BoundIn.TFoT. exact B. } exact F.
    + apply covering. apply UsedIn.FoT. exact U.
    + apply Map.overwrite_if_present_overwrite in F as [[-> ->] | [N F]]. { reflexivity. }
      apply no_capture. { apply BoundIn.TFoB. exact B. } exact F.
    + eapply Map.in_overwrite_if_present. { apply Map.overwrite_if_present_overwrite. }
      destruct (Name.spec x0 variable); [left | right]. { exact Y. }
      apply covering. apply UsedIn.FoB. { exact N. } exact U.
  - edestruct IHterm1; [| | edestruct IHterm2; [| | eexists; econstructor; try eassumption]]; intros.
    5: { apply BoundIn.pattern_spec. } 5: { apply Map.to_self_to_self. } 5: { apply Map.bulk_overwrite_bulk_overwrite. }
    + apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]].
      * apply Map.to_self_to_self in F as [F ->]. reflexivity.
      * apply no_capture. { apply BoundIn.TCaB. exact B. } exact F.
    + eapply Map.in_bulk_overwrite. { apply Map.bulk_overwrite_bulk_overwrite. }
      rewrite Map.in_to_self. destruct (Map.in_spec (BoundIn.pattern pattern0) x); [left | right]. { exact Y. }
      split. { exact N. } apply covering. apply UsedIn.CaB. 2: { exact U. }
      intro B. apply N. apply BoundIn.pattern_spec. exact B.
    + apply no_capture. { apply BoundIn.TCaO. exact B. } exact F.
    + apply covering. apply UsedIn.CaO. exact U. }
  Unshelve.
  - eapply Map.one_to_one_overwrite. { apply Map.overwrite_if_present_overwrite. }
    split; intros. { eapply O2O; eassumption. } apply no_capture. { constructor. } exact F.
  - eapply Map.one_to_one_bulk_overwrite. { apply Map.bulk_overwrite_bulk_overwrite. }
    split; [| split]; intros. { apply Map.one_to_one_to_self. } { eapply O2O; eassumption. }
    apply Map.to_self_to_self in Ff as [If ->]. eapply no_capture. 2: { exact Fo. }
    apply BoundIn.TCaP. apply BoundIn.pattern_spec. exact If.
Qed.



Fixpoint term lookup t :=
  match t with
  | Term.Mov name => option_map Term.Mov (Map.find lookup name)
  | Term.Ref name => option_map Term.Ref (Map.find lookup name)
  | Term.App function argument =>
      match term lookup function with None => None | Some renamed_function =>
        option_map (Term.App renamed_function) (term lookup argument)
      end
  | Term.For variable type body =>
      match term lookup type with None => None | Some renamed_type =>
        let unshadowed := Map.overwrite variable variable lookup in
        option_map (Term.For variable renamed_type) (term unshadowed body)
      end
  | Term.Cas pattern body_if_match other_cases =>
      match term lookup other_cases with None => None | Some renamed_other_cases =>
        let unshadowed := Map.bulk_overwrite (Map.to_self (BoundIn.pattern pattern)) lookup in
        option_map (fun renamed_body_if_match => Term.Cas pattern renamed_body_if_match renamed_other_cases)
          (term unshadowed body_if_match)
      end
  | _ => Some t
  end.

Lemma term_spec {lookup t} (safe : ExtraSafe lookup t)
  : Reflect.Option (fun renamed_term => exists O2O : Map.OneToOne lookup, Term O2O t renamed_term) (term lookup t).
Proof.
  destruct safe as [O2O [no_capture covering]]. generalize dependent lookup. {
  induction t; intros; simpl term; try solve [constructor; exists O2O; constructor].
  - destruct (Map.find_spec lookup name); constructor. { exists O2O. constructor. exact Y. }
    intros t [O2O' C]. invert C. apply N in F as [].
  - destruct (Map.find_spec lookup name); constructor. { exists O2O. constructor. exact Y. }
    intros t [O2O' C]. invert C. apply N in F as [].
  - destruct (IHt1 _ O2O); intros.
    + apply no_capture. { apply BoundIn.TApF. exact B. } exact F.
    + apply covering. apply UsedIn.ApF. exact U.
    + destruct (IHt2 _ O2O); intros.
      * apply no_capture. { apply BoundIn.TApA. exact B. } exact F.
      * apply covering. apply UsedIn.ApA. exact U.
      * constructor. exists O2O. destruct Y. destruct Y0.
        constructor; eapply term_eq; try reflexivity; try eassumption; apply Map.eq_refl.
      * constructor. intros renamed [O2O' C]. invert C. eapply N. eexists. eassumption.
    + constructor. intros renamed [O2O' C]. invert C. eapply N. eexists. eassumption.
  - destruct (IHt1 _ O2O); intros.
    + apply no_capture. { apply BoundIn.TFoT. exact B. } exact F.
    + apply covering. apply UsedIn.FoT. exact U.
    + edestruct (IHt2 (Map.overriding_add variable variable lookup)); intros.
      * eapply Map.one_to_one_overwrite. { apply Map.overwrite_if_present_overwrite. }
        split; intros. { eapply O2O; eassumption. } apply no_capture. { constructor. } exact F.
      * apply Map.find_overriding_add in F as [[-> ->] | [N F]]. { reflexivity. }
        apply no_capture. { apply BoundIn.TFoB. exact B. } exact F.
      * apply Map.in_overriding_add. destruct (Name.spec x0 variable); [left | right]. { assumption. }
        apply covering. apply UsedIn.FoB. { exact N. } exact U.
      * constructor. exists O2O. destruct Y. destruct Y0. econstructor.
        -- eapply term_eq; try reflexivity. { eassumption. } apply Map.eq_refl.
        -- apply Map.singleton_singleton.
        -- apply Map.overwrite_if_present_overwrite.
        -- eassumption.
      * constructor. intros renamed [O2O' C]. invert C. eapply N.
        eexists. eapply term_eq; try reflexivity. { exact body_renaming. }
        intros k v. cbn in not_shadowed. rewrite not_shadowed. rewrite Map.find_overriding_add. reflexivity.
    + constructor. intros renamed [O2O' C]. invert C. eapply N. eexists. eassumption.
  - destruct (IHt2 _ O2O); intros.
    + apply no_capture. { apply BoundIn.TCaO. exact B. } exact F.
    + apply covering. apply UsedIn.CaO. exact U.
    + edestruct (IHt1 (Map.overriding_union (Map.map (fun k _ => k) (BoundIn.pattern pattern0)) lookup)); intros.
      * eapply Map.one_to_one_bulk_overwrite. { apply Map.bulk_overwrite_bulk_overwrite. }
        split. { apply Map.one_to_one_to_self. } split; intros. { eapply O2O; eassumption. }
        apply Map.to_self_to_self in Ff as [If ->]. apply no_capture. 2: { exact Fo. }
        apply BoundIn.TCaP. apply BoundIn.pattern_spec. exact If.
      * apply Map.bulk_overwrite_bulk_overwrite in F as [F | [N F]].
        -- apply Map.to_self_to_self in F as [I ->]. reflexivity.
        -- apply no_capture. { apply BoundIn.TCaB. exact B. } exact F.
      * fold (Map.to_self (BoundIn.pattern pattern0)).
        eapply Map.in_bulk_overwrite. { apply Map.bulk_overwrite_bulk_overwrite. }
        rewrite Map.in_to_self. destruct (Map.in_spec (BoundIn.pattern pattern0) x0); [left | right]. { assumption. }
        split. { exact N. } apply covering. apply UsedIn.CaB. 2: { exact U. }
        intro B. apply N. apply BoundIn.pattern_spec. exact B.
      * constructor. exists O2O. destruct Y. destruct Y0. econstructor.
        -- eapply term_eq; try reflexivity. { eassumption. } apply Map.eq_refl.
        -- apply BoundIn.pattern_spec.
        -- apply Map.to_self_to_self.
        -- apply Map.bulk_overwrite_bulk_overwrite.
        -- eassumption.
      * constructor. intros renamed [O2O' C]. invert C. eapply N.
        eexists. eapply term_eq; try reflexivity. { exact body_if_match_renaming. }
        fold (Map.to_self (BoundIn.pattern pattern0)). intros k v. cbn in not_shadowed. rewrite not_shadowed.
        assert (A := @Map.bulk_overwrite_bulk_overwrite); cbn in A; rewrite A; clear A.
        split; (intros [F | [N' F]]; [left | right]).
        -- apply Map.to_self_to_self. apply pattern_idem in F as [I ->]. apply find_pattern_bindings in I.
           apply BoundIn.pattern_spec in I. split. { assumption. } reflexivity.
        -- split. 2: { exact F. } intros [v' F']. apply Map.to_self_to_self in F' as [I' ->].
           apply BoundIn.pattern_spec in I'. apply find_pattern_bindings in I'.
           apply N'. exists v'. apply pattern_idem. split. { exact I'. } reflexivity.
        -- apply pattern_idem. apply Map.to_self_to_self in F as [I ->]. apply BoundIn.pattern_spec in I.
           apply find_pattern_bindings in I. split. { exact I. } reflexivity.
        -- split. 2: { exact F. } intros [v' F']. apply pattern_idem in F' as [I' ->].
           apply find_pattern_bindings in I'. apply BoundIn.pattern_spec in I'. eapply N'.
           exists v'. apply Map.to_self_to_self. split. { exact I'. } reflexivity.
    + constructor. intros renamed [O2O' C]. invert C. eapply N. eexists. eassumption. }
  Unshelve.
  - eapply Map.one_to_one_overwrite. { apply Map.overwrite_if_present_overwrite. }
    split; intros. { eapply O2O; eassumption. } apply no_capture. { constructor. } exact F.
  - eapply Map.one_to_one_bulk_overwrite. { apply Map.bulk_overwrite_bulk_overwrite. }
    split. { apply Map.one_to_one_to_self. } split; intros. { eapply O2O; eassumption. }
    apply Map.to_self_to_self in Ff as [If ->]. apply no_capture. 2: { exact Fo. }
    apply BoundIn.TCaP. apply BoundIn.pattern_spec. exact If.
Qed.

Lemma term_iff {lookup t} (safe : ExtraSafe lookup t) renamed_t
  : term lookup t = Some renamed_t <-> exists O2O : Map.OneToOne lookup, Term O2O t renamed_t.
Proof.
  destruct (term_spec safe). 2: { split. { intro D. discriminate D. } intro C. apply N in C as []. }
  split. { intro E. invert E. exact Y. } intros [O2O T]. destruct Y as [O2O' T']. f_equal.
  eapply term_det; try reflexivity; try eassumption. apply Map.eq_refl.
Qed.



Definition Context {lookup : Map.to Name.name} (O2O : Map.OneToOne lookup)
  (context : Context.context) (renamed_context : Context.context) : Prop :=
  (*forall k' v', Map.Find renamed_context k' v' <-> exists k, (Map.Find lookup k k' /\*)
  (*  exists v, (Term lookup v v' /\ Map.Find context k v)).*)
  forall name term, Map.Find context name term <-> exists renamed_name, (Map.Find lookup name renamed_name /\
    exists renamed_term, (Term O2O term renamed_term /\ Map.Find renamed_context renamed_name renamed_term)).
Arguments Context {lookup} O2O context renamed_context/.
