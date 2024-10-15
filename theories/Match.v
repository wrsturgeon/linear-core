From LinearCore Require
  BoundIn
  Context
  Map
  Pattern
  Shape
  Term
  Unshadow
  WellFormed
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



Inductive Strict (context : Context.context) : Pattern.strict -> Term.term -> Context.context -> Prop :=
  | Ctr context_with_matches (E : Map.Eq context context_with_matches) ctor
      : Strict context (Pattern.Ctr ctor) (Term.Ctr ctor) context_with_matches
  | App function_pattern function
      context_with_function_matches (function_matched
        : Strict context function_pattern function context_with_function_matches)
      argument_name (N : forall (I : Map.In context_with_function_matches argument_name), False)
      (* can't match the same name twice in the same pattern ^^^ *)
      argument context_with_matches (A
        : Map.Add argument_name argument context_with_function_matches context_with_matches)
      : Strict context (Pattern.App function_pattern argument_name) (Term.App function argument) context_with_matches
  .
Arguments Strict context strict scrutinee context_with_matches.

Fixpoint strict context strict_pattern scrutinee : option Context.context :=
  match strict_pattern, scrutinee with
  | Pattern.Ctr constructor_pattern, Term.Ctr constructor =>
      if Constructor.eq constructor_pattern constructor then Some context else None
  | Pattern.App function_pattern argument_name, Term.App function argument =>
      match strict context function_pattern function with
      | None => None
      | Some context_with_function_matches =>
          Map.disjoint_add argument_name argument context_with_function_matches
      end
  | _, _ => None
  end.

Lemma strict_det
  c1 p1 t1 m1 (S1 : Strict c1 p1 t1 m1)
  c2 (Ec : Map.Eq c1 c2)
  p2 (Ep : p1 = p2)
  t2 (Et : t1 = t2)
  m2 (S2 : Strict c2 p2 t2 m2)
  : Map.Eq m1 m2.
Proof.
  subst. generalize dependent m2. induction S1; intros; invert S2.
  - eapply Map.eq_trans. { apply Map.eq_sym. eassumption. } eapply Map.eq_trans; eassumption.
  - eapply Map.add_det; try reflexivity; try eassumption. apply IHS1. exact function_matched.
Qed.

Lemma strict_eq
  c1 s1 t1 m1 (S : Strict c1 s1 t1 m1)
  c2 (Ec : Map.Eq c1 c2)
  s2 (Es : s1 = s2)
  t2 (Et : t1 = t2)
  m2 (Em : Map.Eq m1 m2)
  : Strict c2 s2 t2 m2.
Proof.
  subst. rename t2 into t. rename s2 into s. generalize dependent m2. generalize dependent c2. induction S; intros.
  - constructor. eapply Map.eq_trans. 2: { eassumption. }
    eapply Map.eq_trans. 2: { eassumption. } apply Map.eq_sym. exact Ec.
  - econstructor. { apply IHS. { exact Ec. } apply Map.eq_refl. } { exact N. }
    eapply Map.add_eq; try reflexivity; try eassumption. apply Map.eq_refl.
Qed.

Lemma strict_spec context strict_pattern scrutinee
  : Reflect.Option (Strict context strict_pattern scrutinee) (strict context strict_pattern scrutinee).
Proof.
  generalize dependent scrutinee. induction strict_pattern; intros;
  destruct scrutinee; try solve [constructor; intros t C; invert C].
  - unfold strict. destruct (Constructor.eq_spec constructor constructor0); constructor.
    + subst. constructor. apply Map.eq_refl.
    + intros t C. invert C. apply N. reflexivity.
  - simpl strict. destruct (IHstrict_pattern scrutinee1) as [function_matches function_matched | N]. 2: {
      constructor. intros t C. invert C. apply N in function_matched as []. }
    destruct (Map.find_spec function_matches argument) as [duplicated F | N]. 2: {
      constructor. econstructor. { eassumption. } { intros [y F]. apply N in F as []. }
      apply Map.add_overriding. cbn. intros. apply N in F as []. }
    constructor. intros t C. invert C. apply N; clear N. eexists.
    eapply strict_det; try reflexivity; [eassumption | | | eassumption];
    try eassumption. apply Map.eq_refl.
Qed.

Lemma in_strict {context strict scrutinee context_with_matches} (S : Strict context strict scrutinee context_with_matches) x
  : Map.In context_with_matches x <-> (BoundIn.Strict strict x \/ Map.In context x).
Proof.
  generalize dependent x. induction S; intros.
  - erewrite Map.in_eq. 2: { apply Map.eq_sym. exact E. }
    split. { intro I. right. exact I. } intros [B | I]. { invert B. } exact I.
  - split.
    + intros [y F]. apply A in F as [[-> ->] | F]. { left. left. }
      eassert (I : Map.In _ _). { eexists. exact F. }
      apply IHS in I as [B | I]; [left | right]. { right. exact B. } exact I.
    + intro I. eapply Map.in_add. { eassumption. }
      destruct I as [B | I]; [invert B; [left; reflexivity |] |];
      right; apply IHS; [left | right]; assumption.
Qed.

Lemma strict_wf {context strict scrutinee context_with_matches} (S : Strict context strict scrutinee context_with_matches)
  : WellFormed.Strict strict.
Proof. induction S; constructor. { exact IHS. } intro B. apply N. eapply in_strict. { exact S. } left. exact B. Qed.

Definition CompatibleStrict (context : Context.context) strict : Prop :=
  forall x (I : Map.In context x) (B : BoundIn.Strict strict x), False.
Arguments CompatibleStrict context strict/.

Lemma compatible_strict_iff strict (WF : WellFormed.Strict strict) context
  : CompatibleStrict context strict <->
    exists scrutinee context_with_matches,
    Strict context strict scrutinee context_with_matches.
Proof.
  split.
  - induction WF; intros. { do 2 eexists. constructor. apply Map.eq_refl. }
    edestruct IHWF as [scrutinee [context_with_matches IH]]; clear IHWF. {
      intros x I B. eapply H. { exact I. } constructor. exact B. }
    assert (N' : ~Map.In context_with_matches argument). { intro I.
      eapply in_strict in I as [I | I]; [| | exact IH]. { apply N in I as []. } apply H in I as []. constructor. }
    eexists. eexists. econstructor. { exact IH. } { exact N'. }
    apply Map.add_overriding. intros v' F. eassert (I : Map.In _ _). { eexists. exact F. } apply N' in I as [].
  - intros [scrutinee [context_with_matches S]] k I B. generalize dependent k. generalize dependent WF.
    induction S; intros. { invert B. } invert B. { apply N. eapply in_strict. { exact S. } right. exact I. }
    invert WF. eapply IHS. { exact curried_well_formed. } { exact I. } exact bound_earlier.
  Unshelve. repeat constructor.
Qed.

Lemma compatible_strict_eq {c1 p1} (C : CompatibleStrict c1 p1) {c2} (Ec : Map.Eq c1 c2) {p2} (Ep : p1 = p2)
  : CompatibleStrict c2 p2.
Proof. subst. intros x I B. eapply C. { eapply Map.in_eq. { exact Ec. } exact I. } exact B. Qed.

Definition compatible_strict (context : Context.context) strict :=
  Map.disjoint context (BoundIn.strict strict).
Arguments compatible_strict context strict/.

Lemma compatible_strict_spec context strict
  : Reflect.Bool (CompatibleStrict context strict) (compatible_strict context strict).
Proof.
  eapply Reflect.bool_eq. 2: { apply Map.disjoint_spec. }
  split; intros F k I B; (eapply F; [exact I |]); apply BoundIn.strict_iff; exact B.
Qed.



Inductive StrictRef (context : Context.context) : Pattern.strict -> Term.term -> Term.term -> Context.context -> Prop :=
  | CtrR context_with_matches (E : Map.Eq context context_with_matches) ctor
      : StrictRef context (Pattern.Ctr ctor) (Term.Ctr ctor) (Term.Ctr ctor) context_with_matches
  | AppR
      function_pattern function context_with_function_matches function_cleaved (function_matched
        : StrictRef context function_pattern function function_cleaved context_with_function_matches)
      argument_name (N : forall (I : Map.In context_with_function_matches argument_name), False)
      (* can't match the same name twice in the same pattern ^^^ *)
      argument context_with_matches (A
        : Map.Add argument_name argument context_with_function_matches context_with_matches)
      : StrictRef context
        (Pattern.App function_pattern argument_name)
        (Term.App function argument)
        (Term.App function_cleaved (Term.Var argument_name Ownership.Owned))
        context_with_matches
  .
Arguments StrictRef context strict scrutinee cleaved context_with_matches.

Fixpoint strict_ref context pattern scrutinee : option (Term.term * Context.context) :=
  match pattern, scrutinee with
  | Pattern.Ctr constructor_pattern, Term.Ctr constructor =>
      if Constructor.eq constructor_pattern constructor then Some (Term.Ctr constructor, context) else None
  | Pattern.App function_pattern argument_name, Term.App function argument =>
      match strict_ref context function_pattern function with
      | None => None
      | Some (function_cleaved, context_with_function_matches) =>
          match Map.disjoint_add argument_name argument context_with_function_matches with
          | None => None
          | Some context_with_matches =>
              Some (Term.App function_cleaved (Term.Var argument_name Ownership.Owned), context_with_matches)
          end
      end
  | _, _ => None
  end.

Lemma strict_ref_det
  {c1 p1 t1 y1 m1} (S1 : StrictRef c1 p1 t1 y1 m1)
  {c2} (Ec : Map.Eq c1 c2)
  {p2} (Ep : p1 = p2)
  {t2} (Et : t1 = t2)
  {y2 m2} (S2 : StrictRef c2 p2 t2 y2 m2)
  : y1 = y2 /\ Map.Eq m1 m2.
Proof.
  subst. generalize dependent m2. generalize dependent y2. induction S1; intros; invert S2.
  - split. { reflexivity. } eapply Map.eq_trans. { apply Map.eq_sym. eassumption. } eapply Map.eq_trans; eassumption.
  - specialize (IHS1 _ _ function_matched) as [<- IH]. split. { reflexivity. }
    eapply Map.add_det; try reflexivity; eassumption.
Qed.

Lemma strict_ref_eq
  c1 s1 t1 y1 m1 (S : StrictRef c1 s1 t1 y1 m1)
  c2 (Ec : Map.Eq c1 c2)
  s2 (Es : s1 = s2)
  t2 (Et : t1 = t2)
  y2 (Ey : y1 = y2)
  m2 (Em : Map.Eq m1 m2)
  : StrictRef c2 s2 t2 y2 m2.
Proof.
  subst. rename t2 into t. rename s2 into s. generalize dependent m2. generalize dependent c2. induction S; intros.
  - constructor. eapply Map.eq_trans. 2: { eassumption. }
    eapply Map.eq_trans. 2: { eassumption. } apply Map.eq_sym. exact Ec.
  - econstructor. { apply IHS. { exact Ec. } apply Map.eq_refl. } { exact N. }
    eapply Map.add_eq; try reflexivity; try eassumption. apply Map.eq_refl.
Qed.

Lemma strict_ref_spec context pattern scrutinee
  : Reflect.Option
    (fun pair => StrictRef context pattern scrutinee (fst pair) (snd pair))
    (strict_ref context pattern scrutinee).
Proof.
  generalize dependent scrutinee. induction pattern; intros;
  destruct scrutinee; try solve [constructor; intros t C; invert C].
  - unfold strict_ref. destruct (Constructor.eq_spec constructor constructor0); constructor.
    + subst. constructor. apply Map.eq_refl.
    + intros t C. invert C. apply N. reflexivity.
  - simpl strict_ref. destruct (IHpattern scrutinee1) as [[cleaved function_matches] function_matched | N]. 2: {
      constructor. intros t C. invert C. apply (N (_, _)) in function_matched as []. }
    destruct (Map.find_spec function_matches argument) as [duplicated F | N]. 2: {
      constructor. econstructor. { eassumption. } { intros [y F]. apply N in F as []. }
      apply Map.add_overriding. cbn. intros. apply N in F as []. }
    constructor. intros t C. invert C. apply N; clear N. eexists.
    eapply strict_ref_det; try reflexivity; [eassumption | | | eassumption];
    try eassumption. apply Map.eq_refl.
Qed.

Lemma in_strict_ref {context strict scrutinee cleaved context_with_matches}
  (S : StrictRef context strict scrutinee cleaved context_with_matches) x
  : Map.In context_with_matches x <-> (BoundIn.Strict strict x \/ Map.In context x).
Proof.
  generalize dependent x. induction S; intros.
  - erewrite Map.in_eq. 2: { apply Map.eq_sym. exact E. }
    split. { intro I. right. exact I. } intros [B | I]. { invert B. } exact I.
  - split.
    + intros [y F]. apply A in F as [[-> ->] | F]. { left. left. }
      eassert (I : Map.In _ _). { eexists. exact F. }
      apply IHS in I as [B | I]; [left | right]. { right. exact B. } exact I.
    + intro I. eapply Map.in_add. { eassumption. }
      destruct I as [B | I]; [invert B; [left; reflexivity |] |];
      right; apply IHS; [left | right]; assumption.
Qed.

Lemma in_strict_ref_context {context name looked_up} (lookup : Map.Find context name looked_up)
  {strict scrutinee cleaved context_with_matches} (S : StrictRef context strict scrutinee cleaved context_with_matches)
  : Map.Find context_with_matches name looked_up.
Proof.
  generalize dependent looked_up. generalize dependent name. induction S; intros. { apply E. exact lookup. }
  apply A. right. apply IHS. exact lookup.
Qed.

Lemma compatible_strict_ref_iff strict (WF : WellFormed.Strict strict) context
  : CompatibleStrict context strict <->
    exists scrutinee cleaved context_with_matches,
    StrictRef context strict scrutinee cleaved context_with_matches.
Proof.
  split.
  - induction WF; intros. { do 3 eexists. constructor. apply Map.eq_refl. }
    edestruct IHWF as [scrutinee [cleaved [context_with_matches IH]]]; clear IHWF. {
      intros x I B. eapply H. { exact I. } constructor. exact B. }
    assert (N' : ~Map.In context_with_matches argument). { intro I.
      eapply in_strict_ref in I as [I | I]; [| | exact IH]. { apply N in I as []. } apply H in I as []. constructor. }
    eexists. do 2 eexists. econstructor. { exact IH. } { exact N'. }
    apply Map.add_overriding. intros v' F. eassert (I : Map.In _ _). { eexists. exact F. } apply N' in I as [].
  - intros [scrutinee [cleaved [context_with_matches S]]] k I B. generalize dependent k. generalize dependent WF.
    induction S; intros. { invert B. } invert B. { apply N. eapply in_strict_ref. { exact S. } right. exact I. }
    invert WF. eapply IHS. { exact curried_well_formed. } { exact I. } exact bound_earlier.
  Unshelve. repeat constructor.
Qed.

Lemma not_bound_in_cleaved {context strict scrutinee cleaved context_with_matches}
  (S : StrictRef context strict scrutinee cleaved context_with_matches)
  {x} (B : BoundIn.Term cleaved x)
  : False.
Proof. induction S. { invert B. } invert B. { apply IHS in bound_in_function as []. } invert bound_in_argument. Qed.



Variant MoveOrReference (context : Context.context) : Pattern.move_or_reference -> Term.term -> Context.context -> Prop :=
  | Mov strict scrutinee context_with_matches (S : Strict context strict scrutinee context_with_matches)
      : MoveOrReference context (Pattern.Mov strict) scrutinee context_with_matches
  | Ref {symlink name scrutinee} (follow_references
        : Context.FollowReferences context symlink name scrutinee)
      strict old_context_with_matches cleaved (S : StrictRef context strict scrutinee cleaved old_context_with_matches)
      context_with_matches (OW : Map.Overwrite name cleaved old_context_with_matches context_with_matches)
      : MoveOrReference context (Pattern.Ref strict) (Term.Var symlink Ownership.Referenced) context_with_matches
  .
Arguments MoveOrReference context strict scrutinee context_with_matches.

Example match_referenced_application ctor arg argn name (N : argn <> name)
  : let pattern := Pattern.Ref (Pattern.App (Pattern.Ctr ctor) argn) in
    let scrutinee := Term.App (Term.Ctr ctor) arg in
    let context := Map.overriding_add name scrutinee Map.empty in
    let context_with_matches :=
      (* Note how each right-hand branch is turned into a `Mov` referencing the contents of the branch: *)
      Map.overriding_add name (Term.App (Term.Ctr ctor) (Term.Var argn Ownership.Owned)) (
      Map.overriding_add argn arg (
      Map.empty)) in
    MoveOrReference context pattern (Term.Var name Ownership.Referenced) context_with_matches.
Proof.
  cbn. econstructor.
  - econstructor.
    + apply Map.find_overriding_add. left. split; reflexivity.
    + intros ? D. discriminate D.
  - econstructor.
    + constructor. intros x y. rewrite Map.find_singleton. rewrite Map.find_overriding_add.
      split. { intros [[-> ->] | [N' F]]. { split; reflexivity. } invert F. }
      intros [-> ->]. left. split; reflexivity.
    + intro I. apply Map.in_singleton in I. apply N in I as [].
    + apply Map.add_overriding. cbn. intros. apply Map.find_singleton in F as [Ea Ev]. apply N in Ea as [].
  - split. { apply Map.in_overriding_add. right. apply Map.in_singleton. reflexivity. } split.
    + intro F. apply Map.find_overriding_add in F as [[-> ->] | [N' F]]; [left | right]. { split; reflexivity. }
      split. { exact N'. } apply Map.find_overriding_add.
      apply Map.find_overriding_add in F as [[-> ->] | [N'' F]]; [left | right]. { split; reflexivity. }
      split. { exact N''. } invert F.
    + intro F. apply Map.find_overriding_add. destruct F as [[-> ->] | [N' F]]; [left | right]. { split; reflexivity. }
      split. { exact N'. } apply Map.find_overriding_add.
      apply Map.find_overriding_add in F as [[-> ->] | [N'' F]]. { left. split; reflexivity. }
      apply Map.find_singleton in F as [E ->]. apply N' in E as [].
Qed.

Example match_referenced_application_deep ctor arg1 arg2 arg1n arg2n name
  (N1 : arg1n <> name) (N2 : arg2n <> name) (N : arg2n <> arg1n)
  : let pattern := Pattern.Ref (Pattern.App (Pattern.App (Pattern.Ctr ctor) arg1n) arg2n) in
    let scrutinee := Term.App (Term.App (Term.Ctr ctor) arg1) arg2 in
    let context := Map.overriding_add name scrutinee Map.empty in
    let context_with_matches :=
      (* Note how each right-hand branch is turned into a `Mov` referencing the contents of the branch: *)
      Map.overriding_add name (Term.App
        (Term.App (Term.Ctr ctor) (Term.Var arg1n Ownership.Owned))
        (Term.Var arg2n Ownership.Owned)
      ) $ Map.overriding_add arg1n arg1 $ Map.overriding_add arg2n arg2 Map.empty in
    MoveOrReference context pattern (Term.Var name Ownership.Referenced) context_with_matches.
Proof.
  cbn. econstructor.
  - econstructor.
    + apply Map.find_overriding_add. left. split; reflexivity.
    + intros ? D. discriminate D.
  - econstructor.
    + econstructor.
      * constructor. intros x y. rewrite Map.find_singleton. rewrite Map.find_overriding_add.
        split. { intros [[-> ->] | [N' F]]. { split; reflexivity. } invert F. }
        intros [-> ->]. left. split; reflexivity.
      * intro I. apply Map.in_singleton in I. apply N1 in I as [].
      * apply Map.add_overriding. cbn. intros. apply Map.find_singleton in F as [Ea Ev]. apply N1 in Ea as [].
    + intro I. apply Map.in_overriding_add in I as [E | I]. { apply N in E as []. }
      apply Map.in_singleton in I. apply N2 in I as [].
    + apply Map.add_overriding. cbn. intros.
      apply Map.find_overriding_add in F as [[Ea Ev] | [N' F]]. { apply N in Ea as []. }
      apply Map.find_singleton in F as [Ea Ev]. apply N2 in Ea as [].
  - split. { apply Map.in_overriding_add. right. apply Map.in_overriding_add. right. apply Map.in_singleton. reflexivity. }
    split.
    + intro F. apply Map.find_overriding_add in F as [[-> ->] | [N' F]]; [left | right]. { split; reflexivity. }
      split. { exact N'. } apply Map.find_overriding_add. rewrite Map.find_overriding_add.
      apply Map.find_overriding_add in F as [[-> ->] | [N'' F]]. {
        right. split. { symmetry. exact N. } left. split; reflexivity. }
      apply Map.find_overriding_add in F as [[-> ->] | [N''' F]]; [left | right]. { split; reflexivity. } invert F.
    + intro F. apply Map.find_overriding_add. destruct F as [[-> ->] | [N' F]]; [left | right]. { split; reflexivity. }
      split. { exact N'. } apply Map.find_overriding_add. rewrite Map.find_overriding_add.
      apply Map.find_overriding_add in F as [[-> ->] | [N'' F]]. { right. split. { exact N. } left. split; reflexivity. }
      apply Map.find_overriding_add in F as [[-> ->] | [N''' F]]; [left | right]. { split; reflexivity. }
      apply Map.find_singleton in F as [E ->]. apply N' in E as [].
Qed.

Definition move_or_reference context pattern scrutinee :=
  match pattern with
  | Pattern.Mov s =>
      match strict context s scrutinee with
      | None => None
      | Some context_with_matches => Some context_with_matches
      end
  | Pattern.Ref s =>
      match scrutinee with
      | Term.Var symlink Ownership.Referenced =>
          match Context.follow_references context symlink with None => None | Some (name, term) =>
            match strict_ref context s term with None => None | Some (cleaved, context_with_matches) =>
              Some $ Map.overwrite name cleaved context_with_matches
            end
          end
      | _ => None
      end
  end.

Lemma move_or_reference_det
  c1 p1 t1 m1 (S1 : MoveOrReference c1 p1 t1 m1)
  c2 (Ec : Map.Eq c1 c2)
  p2 (Ep : p1 = p2)
  t2 (Et : t1 = t2)
  m2 (S2 : MoveOrReference c2 p2 t2 m2)
  : Map.Eq m1 m2.
Proof.
  subst. invert S1; invert S2. { eapply strict_det; try reflexivity; eassumption. }
  destruct (Context.follow_references_det follow_references Ec eq_refl follow_references0) as [<- <-].
  destruct (strict_ref_det S Ec eq_refl eq_refl S0) as [<- Eo]. eapply Map.overwrite_det; try eassumption; reflexivity.
Qed.

Lemma move_or_reference_eq
  c1 p1 t1 m1 (MR : MoveOrReference c1 p1 t1 m1)
  c2 (Ec : Map.Eq c1 c2)
  p2 (Ep : p1 = p2)
  t2 (Et : t1 = t2)
  m2 (Em : Map.Eq m1 m2)
  : MoveOrReference c2 p2 t2 m2.
Proof.
  invert MR.
  - constructor. eapply strict_eq; try reflexivity; eassumption.
  - econstructor.
    + eapply Context.follow_references_eq. { exact follow_references. } { exact Ec. } { reflexivity. } { reflexivity. } reflexivity.
    + eapply strict_ref_eq; try reflexivity; try eassumption. apply Map.eq_refl.
    + eapply Map.overwrite_eq; try reflexivity; try eassumption. apply Map.eq_refl.
Qed.

Lemma in_move_or_reference {context move_or_reference scrutinee context_with_matches}
  (MR : MoveOrReference context move_or_reference scrutinee context_with_matches) x
  : Map.In context_with_matches x <-> (BoundIn.MoveOrReference move_or_reference x \/ Map.In context x).
Proof.
  invert MR.
  - erewrite in_strict. 2: { exact S. } split; (intros [B | I]; [left | right; exact I]). { constructor. exact B. }
    invert B. exact bound_in_strict.
  - erewrite Map.in_overwrite. 2: { exact OW. } erewrite in_strict_ref. 2: { exact S. }
    split; (intros [B | I]; [left | right; exact I]). { constructor. exact B. } invert B. exact bound_in_strict.
Qed.

Lemma move_or_reference_spec context pattern scrutinee
  : Reflect.Option (MoveOrReference context pattern scrutinee) (move_or_reference context pattern scrutinee).
Proof.
  destruct pattern; cbn.
  - cbn. destruct (strict_spec context strict0 scrutinee); constructor. { constructor. exact Y. }
    intros x MR. invert MR. apply N in S as [].
  - destruct scrutinee; try (constructor; intros m C; invert C). destruct ownership. { constructor. intros m C. invert C. }
    destruct (Context.follow_references_spec context name). 2: {
      constructor. intros m C. invert C. apply (N (_, _)) in follow_references as []. }
    destruct x as [k v]. cbn in *. destruct (strict_ref_spec context strict0 v) as [[cleaved context_with_matches] |]. 2: {
      constructor. intros m C. invert C. destruct (Context.follow_references_det Y (Map.eq_refl _) eq_refl follow_references).
      subst. apply (N (_, _)) in S as []. }
    cbn in *. constructor. econstructor; try eassumption. apply Map.overwrite_overwrite.
    eapply in_strict_ref. { exact Y0. } right. apply Context.follow_references_find in Y. eexists. exact Y.
Qed.

Variant CompatibleMoveOrReference context : Pattern.move_or_reference -> Prop :=
  | CRef strict (strict_compatible : CompatibleStrict context strict) (* counterproductive to traverse an arbitrary graph of indirection *)
      : CompatibleMoveOrReference context (Pattern.Ref strict)
  | CMov strict (strict_compatible : CompatibleStrict context strict)
      : CompatibleMoveOrReference context (Pattern.Mov strict)
  .

Lemma compatible_move_or_reference_eq {c1 p1} (C : CompatibleMoveOrReference c1 p1) {c2} (Ec : Map.Eq c1 c2) {p2} (Ep : p1 = p2)
  : CompatibleMoveOrReference c2 p2.
Proof. subst. invert C; constructor; eapply compatible_strict_eq; try reflexivity; eassumption. Qed.

Definition compatible_move_or_reference (context : Context.context) move_or_reference :=
  Map.disjoint context (BoundIn.move_or_reference move_or_reference).
Arguments compatible_move_or_reference context move_or_reference/.

Lemma compatible_move_or_reference_spec context move_or_reference
  : Reflect.Bool
    (CompatibleMoveOrReference context move_or_reference)
    (compatible_move_or_reference context move_or_reference).
Proof.
  eapply Reflect.bool_eq. 2: { apply Map.disjoint_spec. }
  destruct move_or_reference; (split; intro F; [invert F | constructor]); intros k I B.
  - eapply strict_compatible. { exact I. } apply BoundIn.strict_iff. exact B.
  - eapply F. { exact I. } apply BoundIn.strict_iff. exact B.
  - eapply strict_compatible. { exact I. } apply BoundIn.strict_iff. exact B.
  - eapply F. { exact I. } apply BoundIn.strict_iff. exact B.
Qed.



Variant Pattern (context : Context.context) : Pattern.pattern -> Term.term -> Context.context -> Prop :=
  | Nam
      name (N : forall (I : Map.In context name), False)
      scrutinee context_with_matches (S : Map.Add name scrutinee context context_with_matches)
      : Pattern context (Pattern.Nam name) scrutinee context_with_matches
  | Pat
      move_or_reference scrutinee context_with_matches (move_or_reference_matched
        : MoveOrReference context move_or_reference scrutinee context_with_matches)
      : Pattern context (Pattern.Pat move_or_reference) scrutinee context_with_matches
  .
Arguments Pattern context pattern scrutinee context_with_matches.

Definition pattern context patt scrutinee :=
  match patt with
  | Pattern.Nam name => Map.disjoint_add name scrutinee context
  | Pattern.Pat mor => move_or_reference context mor scrutinee
  end.

Lemma pattern_det
  c1 p1 t1 m1 (P1 : Pattern c1 p1 t1 m1)
  c2 (Ec : Map.Eq c1 c2)
  p2 (Ep : p1 = p2)
  t2 (Et : t1 = t2)
  m2 (P2 : Pattern c2 p2 t2 m2)
  : Map.Eq m1 m2.
Proof.
  invert P1; invert P2.
  - eapply Map.add_det; try reflexivity; eassumption.
  - eapply move_or_reference_det; try reflexivity; eassumption.
Qed.

Lemma pattern_eq
  c1 p1 t1 m1 (P : Pattern c1 p1 t1 m1)
  c2 (Ec : Map.Eq c1 c2)
  p2 (Ep : p1 = p2)
  t2 (Et : t1 = t2)
  m2 (Em : Map.Eq m1 m2)
  : Pattern c2 p2 t2 m2.
Proof.
  invert P.
  - constructor. { intro I. eapply Map.in_eq in I. { apply N in I as []. } exact Ec. }
    eapply Map.add_eq; try reflexivity; eassumption.
  - constructor. eapply move_or_reference_eq; try reflexivity; try eassumption.
Qed.

Lemma pattern_spec context patt scrutinee
  : Reflect.Option (Pattern context patt scrutinee) (pattern context patt scrutinee).
Proof.
  destruct patt; cbn.
  - destruct (Map.find_spec context name); constructor. { intros m C. invert C. apply N. eexists. exact Y. }
    constructor. { intros [y F]. eapply N. exact F. } apply Map.add_overriding. cbn. intros. apply N in F as [].
  - destruct (move_or_reference_spec context move_or_reference0 scrutinee); constructor. { constructor. exact Y. }
    intros ctx C. invert C. apply N in move_or_reference_matched as [].
Qed.

Lemma pattern_iff context patt scrutinee context_with_matches
  : Pattern context patt scrutinee context_with_matches <-> exists context_with_matches', (
    pattern context patt scrutinee = Some context_with_matches' /\ Map.Eq context_with_matches' context_with_matches).
Proof.
  destruct (pattern_spec context patt scrutinee). 2: {
    split. { intro P. apply N in P as []. } intros [context_with_matches' [D E]]. discriminate D. }
  split.
  - intro P. eexists. split. { reflexivity. }
    eapply pattern_det; try reflexivity; try eassumption. apply Map.eq_refl.
  - intros [context_with_matches' [tmp E]]. invert tmp.
    eapply pattern_eq; try reflexivity; try eassumption. apply Map.eq_refl.
Qed.

Variant Compatible context : Pattern.pattern -> Prop :=
  | CNam name (N : forall (I : Map.In context name), False)
      : Compatible context (Pattern.Nam name)
  | CPat move_or_reference (move_or_reference_compatible : CompatibleMoveOrReference context move_or_reference)
      : Compatible context (Pattern.Pat move_or_reference)
  .

Lemma compatible_eq {c1 p1} (C : Compatible c1 p1) {c2} (Ec : Map.Eq c1 c2) {p2} (Ep : p1 = p2)
  : Compatible c2 p2.
Proof.
  subst. invert C. { constructor. intro I. apply N. eapply Map.in_eq. { exact Ec. } exact I. }
  constructor. eapply compatible_move_or_reference_eq; try reflexivity; eassumption.
Qed.

Definition compatible (context : Context.context) pattern :=
  Map.disjoint context (BoundIn.pattern pattern).
Arguments compatible context pattern/.

Lemma compatible_spec context pattern
  : Reflect.Bool
    (Compatible context pattern)
    (compatible context pattern).
Proof.
  eapply Reflect.bool_eq. 2: { apply Map.disjoint_spec. } split; intro F.
  - invert F.
    + intros k I B. apply N. apply Map.in_singleton in B as ->. exact I.
    + intros k I B. invert move_or_reference_compatible; (eapply strict_compatible; [exact I |]);
      apply BoundIn.strict_iff; exact B.
  - destruct pattern; simpl BoundIn.pattern in *.
    + constructor. intro I. eapply F. { exact I. } apply Map.in_singleton. reflexivity.
    + constructor. destruct move_or_reference0; simpl BoundIn.move_or_reference in *; constructor;
      intros k I B; (eapply F; [exact I |]); apply BoundIn.strict_iff; exact B.
Qed.

Lemma compatible_iff context pattern
  : Compatible context pattern <-> compatible context pattern = true.
Proof. exact (Reflect.bool_iff (compatible_spec _ _)). Qed.



(*
Lemma unshadow_strict
  {context scrutinee} (WF : Unshadow.WellFormedInContext context scrutinee)
  {pattern context_with_matches} (M : Strict context pattern scrutinee context_with_matches)
  : Unshadow.WellFormedContext context_with_matches.
Proof.
  cbn. generalize dependent WF. induction M; intros; cbn in *.
  - eapply WF. 2: { apply E. exact F. } intro x. rewrite <- D. eapply Map.in_eq. exact E.
  - destruct WF as [WFc WFt]. specialize (WFt _ $ Map.domain_domain _). invert WFt.
    eassert (WF' : _); [| specialize (IHM WF')]. { split. { exact WFc. }
      intros d' D'. eapply Unshadow.cant_bind_subset; [eapply Unshadow.context_superset; [exact WFf |] |]; intros x [] F'. {
        apply Map.find_domain in F'. apply D' in F' as [[] F']. exact F'. }
      eassert (I : Map.In _ _). { exists tt. exact F'. }
      apply D' in I. eassert (I' : @Map.In unit _ _). 2: { destruct I' as [[] F'']. exact F''. }
      apply Uf. left. apply Map.in_domain. exact I. }
    eassert (D' : Map.Domain context_with_function_matches $ Map.set_union _ _); [| specialize (IHM _ D')]. {
      intro x. rewrite (in_strict M). rewrite <- (BoundIn.strict_iff function_pattern x).
      rewrite <- (Map.in_domain _ context). symmetry. apply Map.in_overriding_union. }
    apply A in F as [[-> ->] | F]. {
      eapply Unshadow.cant_bind_subset; [eapply Unshadow.context_superset; [exact WFa |] |].
      * intros k [] I. apply Map.find_domain in I. specialize (D k) as [[[] F] _]. 2: { exact F. }
        destruct (in_strict M k) as [_ IS]. specialize (IS $ or_intror I) as [v F]. exists v. apply A. right. exact F.
      * intros k [] F. specialize (Ua k) as [_ [[] Ua]]. 2: { exact Ua. } rewrite Map.in_domain.
        specialize (D k) as [_ D]. eassert (I : Map.In domain k). { eexists. exact F. }
        clear F. specialize (D I) as [v F]. clear I. apply A in F as [[-> ->] | F].
        -- admit.
        -- eassert (IS := in_strict M k).



    2: { specialize (IHM _ _ F).
      eapply Unshadow.cant_bind_union; [eapply Unshadow.context_superset; [exact IHM |] | |].
      * intros x [] I. assert (A' : x = argument_name \/ Map.In context_with_function_matches x). 2: {
          eassert (I' : @Map.In unit _ _). 2: { destruct I' as [[] F']. exact F'. } apply D.
          destruct A' as [-> | [y F']]. { exists argument. apply A. left. split; reflexivity. } exists y. apply A. right. exact F'. }
        unfold Map.Domain in D'; rewrite D'; clear D'. rewrite Map.in_overriding_union. rewrite Map.in_domain.
        destruct (String.eqb_spec x argument_name); [left | right]. { exact e. }
        apply Map.union_set in I as [B | I]; [left | right]. { exists tt. exact B. } apply Map.find_domain in I. exact I.
      * intros x []. split.
        -- intro F'. eassert (I : Map.In _ _). { exists tt. exact F'. } clear F'. apply D in I as [y F'].
           apply A in F' as [[-> ->] | F']; [right | left]. { apply Map.find_singleton. split; reflexivity. }
           apply Map.union_set. eassert (I : Map.In _ _). { exists y. exact F'. }
           eapply (in_strict M) in I as [B | I]; [left | right]. { apply BoundIn.strict_iff in B as [[] B]. exact B. }
           apply Map.find_domain. exact I.
        -- intros FF. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. } apply D. destruct FF as [F' | F']. 2: {
             apply Map.find_singleton in F' as [-> _]. exists argument. apply A. left. split; reflexivity. }
           destruct (in_strict M x) as [_ [y IS]]. 2: { exists y. apply A. right. exact IS. }
           apply Map.union_set in F' as [F' | F']; [left | right]. { apply BoundIn.strict_iff. exists tt. exact F'. }
           apply Map.find_domain in F'. exact F'.
      * intros x B I. apply Map.in_singleton in I as ->.



Check Unshadow.unshadow_context_spec.
Fail "use the above!".



    apply A in F as [[-> ->] | F]. 2: { eapply IHM. 3: { exact F. } 2: { exact D. }
    + eapply Unshadow.cant_bind_subset; [eapply Unshadow.context_superset; [eapply IHM |] |].
      * intros x [] I. apply Map.find_domain in I. eapply or_intror in I. apply (in_strict M) in I as [y F].
        eassert (I' : @Map.In unit _ _). 2: { destruct I' as [[] F']. exact F'. } apply D. exists y. apply A. right. exact F.
      * intros x [] F. eassert (I : Map.In _ _). { exists tt. exact F. } clear F. apply D in I as [y F].
        eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. } apply Ua. rewrite Map.in_domain.
        destruct (String.eqb_spec x argument_name). { subst. apply
        apply A in F as [[-> ->] | F]. 2: { left. assert (IS := in_strict M).



  invert Ut. apply A in F as [[-> ->] | F].
  - eapply Unshadow.cant_bind_subset. { exact WFa. }
    intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
    apply Ua. left. exists tt. exact F.
  - eapply IHM. { exact D. } 2: { exact Uc. } 2: { exact F. } eapply Unshadow.cant_bind_subset. { exact WFf. }
    intros x [] F'. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F'']. exact F''. }
    apply Uf. left. exists tt. exact F'.
Qed.

Lemma unshadow_strict_ref {context domain} (D : Map.Domain context domain) {scrutinee} (Ut : Unshadow.WellFormedIn domain scrutinee)
  (Uc : Map.ForAll (fun _ => Unshadow.WellFormedIn domain) context)
  {pattern cleaved context_with_matches} (M : StrictRef context pattern scrutinee cleaved context_with_matches)
  : Unshadow.WellFormedContext context_with_matches cleaved.
  {domain_with_matches} (Dm : Map.Domain context_with_matches domain_with_matches)
  : Unshadow.WellFormedIn domain_with_matches cleaved /\ Map.ForAll (fun _ => Unshadow.WellFormedIn domain_with_matches) context_with_matches.
Proof.
  cbn. generalize dependent Uc. generalize dependent Ut. generalize dependent domain. induction M; intros.
  - split. { constructor. } intros. eapply Uc. apply E. exact F.
  - invert Ut. specialize (IHM _ D) as [IHt IHc].
    + eapply Unshadow.cant_bind_subset. { exact WFf. }
      intros x [] F. eassert (I : @Map.In unit _ _). 2: { destruct I as [[] F']. exact F'. }
      apply Uf. left. exists tt. exact F.
    + exact Uc.
    + split.
      * econstructor; intros.
        -- rewrite <- (BoundIn.term_iff (Term.Var argument_name Ownership.Owned) x).
           rewrite <- (UsedIn.term_iff (Term.Var argument_name Ownership.Owned) x).
           cbn. repeat rewrite <- Map.in_overriding_union. reflexivity.
        -- rewrite <- (BoundIn.term_iff function_cleaved x). rewrite <- (UsedIn.term_iff function_cleaved x).
           repeat rewrite <- Map.in_overriding_union. reflexivity.
        -- eapply Unshadow.cant_bind_union. { exact IHt. } { apply Map.union_set. }
           intros. apply Map.in_overriding_union in I as [I | I]. { apply Map.empty_empty in I as []. }
           apply Map.in_singleton in I as ->. eapply not_bound_in_cleaved in B as []. exact M.
        -- constructor. apply D.



        3: { exact IHt. } { constructor. } 2: { invert Ba. }
        eapply not_bound_in_cleaved in Bf as []. exact M.
      * intros. apply A in F as [[-> ->] | F]. { exact Ua. } eapply IHc; eassumption.
Qed.

Lemma unshadow_move_or_reference {scrutinee} (Ut : Unshadow.Unshadowed scrutinee)
  {context} (Uc : Map.ForAll (fun _ => Unshadow.Unshadowed) context)
  {pattern context_with_matches} (M : MoveOrReference context pattern scrutinee context_with_matches)
  : Map.ForAll (fun _ => Unshadow.Unshadowed) context_with_matches.
Proof.
  invert M.
  - eapply unshadow_strict. { exact Ut. } { exact Uc. } exact S.
  - eapply unshadow_strict_ref in S as [U FA].
    + cbn. intros. apply OW in F as [[-> ->] | [N F]]. { exact U. } eapply FA. exact F.
    + eapply Uc. eapply Context.follow_references_find. exact follow_references.
    + exact Uc.
Qed.

Lemma unshadow_pattern {scrutinee} (Ut : Unshadow.Unshadowed scrutinee)
  {context} (Uc : Map.ForAll (fun _ => Unshadow.Unshadowed) context)
  {pattern context_with_matches} (M : Pattern context pattern scrutinee context_with_matches)
  : Map.ForAll (fun _ => Unshadow.Unshadowed) context_with_matches.
Proof.
  cbn. intros. invert M.
  - apply S in F. destruct F as [[-> ->] | F]. { exact Ut. } eapply Uc. exact F.
  - eapply unshadow_move_or_reference. 3: { exact move_or_reference_matched. } { exact Ut. } { exact Uc. } exact F.
Qed.
*)



Lemma strict_shaped {context pattern scrutinee context_with_matches}
  (M : Strict context pattern scrutinee context_with_matches)
  : Shape.ShapeOf scrutinee Shape.Resource.
Proof. induction M; constructor. exact IHM. Qed.

Lemma strict_ref_shaped {context pattern scrutinee cleaved context_with_matches}
  (M : StrictRef context pattern scrutinee cleaved context_with_matches)
  : Shape.ShapeOf scrutinee Shape.Resource.
Proof. induction M; constructor. exact IHM. Qed.

Lemma follow_references_shaped {context symlink name followed} (FR : Context.FollowReferences context symlink name followed)
  (S : Shape.ShapeOf followed Shape.Resource)
  : Shape.ShapeOrRef context followed Shape.Resource.
Proof. generalize dependent S. induction FR; intros; apply Shape.or_ref; exact S. Qed.

Lemma move_or_reference_shape_or_ref {context pattern scrutinee context_with_matches}
  (M : MoveOrReference context pattern scrutinee context_with_matches)
  : Shape.ShapeOrRef context scrutinee Shape.Resource.
Proof.
  invert M. { apply Shape.or_ref. eapply strict_shaped. exact S. }
  econstructor. { exact follow_references. } eapply strict_ref_shaped. exact S.
Qed.



Lemma pull_out_of_acc add acc (li : list (MapCore.key * Term.term))
  : List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) (add + acc) li =
    add + List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) acc li.
Proof.
  generalize dependent acc. generalize dependent add.
  induction li as [| [k v] tail IH]; intros; cbn in *. { reflexivity. }
  rewrite PeanoNat.Nat.add_assoc. rewrite (PeanoNat.Nat.add_comm add $ Term.nodes v).
  rewrite <- PeanoNat.Nat.add_assoc. f_equal. apply IH.
Qed.

Lemma strict_decreasing {context pattern scrutinee context_with_matches}
  (M : Strict context pattern scrutinee context_with_matches) other_cases
  : List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context_with_matches) <
    Pattern.strict_nodes pattern + Term.nodes other_cases + Term.nodes scrutinee +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context).
Proof.
  generalize dependent other_cases. induction M; intros; cbn in *. {
    rewrite (PeanoNat.Nat.add_comm _ 1). cbn. apply Map.bindings_eq in E as ->.
    repeat rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. }
  eassert (agree : _); [| assert (A' := @Map.add_overriding _ argument_name argument context_with_function_matches agree)]. {
    intros y F. contradiction N. eexists. exact F. }
  eapply Map.add_det in A'; try reflexivity. 2: { exact A. } 2: { apply Map.eq_refl. }
  apply Map.bindings_eq in A' as ->. destruct (Map.bindings_add_split N argument) as [bl [br [E1 E2]]]. rewrite E1.
  rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc. rewrite <- List.fold_right_app. rewrite <- E2.
  rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument). rewrite PeanoNat.Nat.add_succ_r. rewrite PeanoNat.Nat.add_assoc.
  rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument). rewrite PeanoNat.Nat.add_succ_l.
  repeat rewrite <- PeanoNat.Nat.add_assoc. repeat rewrite <- (PeanoNat.Nat.add_succ_r $ Term.nodes argument).
  apply PeanoNat.Nat.add_lt_mono_l. rewrite PeanoNat.Nat.add_assoc. eapply PeanoNat.Nat.lt_trans. { exact (IHM other_cases). }
  eapply PeanoNat.Nat.lt_trans. { apply PeanoNat.Nat.lt_succ_diag_r. }
  apply -> PeanoNat.Nat.succ_lt_mono. rewrite PeanoNat.Nat.add_assoc.
  eapply PeanoNat.Nat.lt_trans. { apply PeanoNat.Nat.lt_succ_diag_r. }
  apply -> PeanoNat.Nat.succ_lt_mono. apply PeanoNat.Nat.lt_succ_diag_r.
Qed.

(*
Lemma no_dup_app {T P} (E : RelationClasses.Equivalence P) {a b : list T} (ND : SetoidList.NoDupA P (a ++ b))
  : SetoidList.NoDupA P a /\ SetoidList.NoDupA P b /\ (forall x, SetoidList.InA P x a -> SetoidList.InA P x b -> False).
Proof.
  generalize dependent b. induction a as [| head tail IH]; intros; cbn in *. {
    split. { constructor. } split. { exact ND. } intros x Ia Ib. invert Ia. }
  invert ND. specialize (IH _ H2) as [IHa [IHb IHd]]. split. 2: {
    split. { exact IHb. } intros. invert H. 2: { eapply IHd; eassumption. }
    apply H1. apply SetoidList.InA_app_iff. right. eapply SetoidList.InA_eqA; eassumption. }
  constructor. 2: { exact IHa. } intro I. apply H1. apply SetoidList.InA_app_iff. left. exact I.
Qed.

Lemma rev_eq {T} (a b : list T)
  : a = b <-> List.rev a = List.rev b.
Proof. split. { intros ->. reflexivity. } intro E. apply List.rev_inj in E as ->. reflexivity. Qed.

Lemma cons_nil_app {T} (x : T) xs
  : ((x :: nil) ++ xs = x :: xs)%list.
Proof. reflexivity. Qed.

Lemma no_dup_tail {T P} {x : T} {xs} (ND : SetoidList.NoDupA P (x :: xs)%list)
  : SetoidList.NoDupA P xs.
Proof. invert ND. assumption. Qed.

Lemma split_align {x1 x2} (N : x1 <> x2)
  {T} (dec : forall a b : T, {a = b} + {a <> b}) {y1 y2 : T}
  {l1 r1} (ND1 : SetoidList.NoDupA MapCore.eq_key (l1 ++ (x1, y1) :: r1)%list)
  {l2 r2} (ND2 : SetoidList.NoDupA MapCore.eq_key (l2 ++ (x2, y2) :: r2)%list)
  (E : (l1 ++ (x1, y1) :: r1)%list = (l2 ++ (x2, y2) :: r2)%list)
  : ((
    exists l3 r3, l1 = l3 ++ (x2, y2) :: r3 /\ r2 = r3 ++ (x1, y1) :: r1
  ) \/ (
    exists l3 r3, r1 = l3 ++ (x2, y2) :: r3 /\ l2 = l1 ++ (x1, y1) :: l3
  ))%list.
Proof.
  apply SetoidList.NoDupA_swap in ND1. 2: { exact Map.eq_key_equiv. }
  apply SetoidList.NoDupA_swap in ND2. 2: { exact Map.eq_key_equiv. }
  invert ND1. invert ND2. rewrite SetoidList.InA_app_iff in *.
  assert (pair_dec : ListDec.decidable_eq (String.string * T)). {
    intros [k1 v1] [k2 v2]. destruct (String.eqb_spec k1 k2). 2: { right. intro D. apply n. invert D. reflexivity. }
    destruct (dec v1 v2); subst; [left | right]. { reflexivity. } intro D. apply n. invert D. reflexivity. }
  destruct (ListDec.In_decidable pair_dec (x2, y2) l1); [left | right].
  - apply List.in_split in H as [l' [r' ->]]. do 2 eexists. split. { reflexivity. }
    rewrite <- List.app_assoc in E. rewrite <- List.app_comm_cons in E. generalize dependent r'. generalize dependent l'.
    generalize dependent r2. generalize dependent r1. induction l2 as [| [k2 v2] l2 IH]; intros; cbn in *.
    + destruct l'; invert E; cbn in *. { reflexivity. }
      contradiction H3. right. apply SetoidList.InA_app_iff. right. left. reflexivity.
    + destruct l'; invert E; cbn in *. { contradiction H3. left. left. reflexivity. } eapply IH; try eassumption.
      * intros [C | C]; apply H3; repeat constructor; exact C.
      * invert H4. assumption.
      * invert H2. apply no_dup_app in H7 as [ND1 [ND2 D]].
        apply SetoidList.NoDupA_app. { exact Map.eq_key_equiv. } { exact ND1. } { exact ND2. } { exact D. } exact Map.eq_key_equiv.
      * intros [C | C]; apply H1; repeat constructor; exact C.
  - destruct (ListDec.In_decidable pair_dec (x2, y2) r1).
    + apply List.in_split in H0 as [l' [r' ->]]. do 2 eexists. split. { reflexivity. }
      apply rev_eq in E. repeat (rewrite List.rev_app_distr in E; cbn in E); repeat rewrite <- List.app_assoc in E; cbn in E.
      generalize dependent r'. generalize dependent l'. generalize dependent l2. generalize dependent l1.
      remember (List.rev r2) as r eqn:R. generalize dependent r2. induction r; intros; cbn in *. {
        apply rev_eq in R. rewrite List.rev_involutive in R. subst. destruct (List.rev r') eqn:R; invert E; cbn in *. {
          apply rev_eq in R. rewrite List.rev_involutive in R. subst. cbn in *.
          apply rev_eq in H5. repeat (rewrite List.rev_app_distr in H5; cbn in H5).
          repeat rewrite List.rev_involutive in H5. subst. rewrite <- List.app_assoc. reflexivity. }
        apply rev_eq in H6. repeat (rewrite List.rev_app_distr in H6; cbn in H6). repeat rewrite List.rev_involutive in H6.
        repeat rewrite <- List.app_assoc in H6. cbn in H6. subst. contradiction H3. left. apply SetoidList.InA_app_iff.
        right. right. apply SetoidList.InA_app_iff. right. left. reflexivity. }
      apply rev_eq in R. cbn in R. rewrite List.rev_involutive in R. subst. destruct (List.rev r') eqn:R; invert E; cbn in *. {
        apply rev_eq in R. rewrite List.rev_involutive in R. cbn in *. subst. contradiction H3. right.
        apply SetoidList.InA_app_iff. right. left. reflexivity. }
      eapply IHr. 7: { rewrite <- H6. f_equal. apply List.rev_involutive. } { symmetry. apply List.rev_involutive. } all: try eassumption.
      * intros [C | C]; apply H3. { left. exact C. } right. apply SetoidList.InA_app_iff. left. exact C.
      * apply no_dup_app in H2 as [ND1 [ND2 D]]. 2: { exact Map.eq_key_equiv. }
        rewrite List.app_assoc in H4. apply no_dup_app in H4 as [ND1' [ND2' D']]. { exact ND1'. } exact Map.eq_key_equiv.
      * apply no_dup_app in H2 as [ND1 [ND2 D]]. 2: { exact Map.eq_key_equiv. }
        apply SetoidList.NoDupA_app. { exact Map.eq_key_equiv. } { exact ND1. } 2: {
          intros. eapply D. { exact H0. } apply SetoidList.InA_app_iff.
          apply SetoidList.InA_app_iff in H2 as [C | C]; [left | right]. { exact C. } invert C; [left | right]. { assumption. }
          apply SetoidList.InA_rev. rewrite R. right. apply SetoidList.InA_rev. assumption. }
        apply no_dup_app in ND2 as [ND1' [ND2' D']]. 2: { exact Map.eq_key_equiv. } invert ND2'.
        apply SetoidList.NoDupA_app. { exact Map.eq_key_equiv. } { exact ND1'. } 2: { intros. eapply D'. { exact H0. }
          invert H2; [left | right]. { assumption. } apply SetoidList.InA_rev. rewrite R. right. apply SetoidList.InA_rev. assumption. }
        constructor. 2: { apply SetoidList.NoDupA_rev. { exact Map.eq_key_equiv. }
          eapply no_dup_tail. rewrite <- R. apply SetoidList.NoDupA_rev. { exact Map.eq_key_equiv. } assumption. }
        intro I. eapply SetoidList.InA_rev in I. rewrite List.rev_involutive in I. eapply SetoidList.InA_cons_tl in I.
        rewrite <- R in I. apply -> SetoidList.InA_rev in I. apply H5 in I as [].
      * intros [C | C]; apply H1. { left. exact C. } right. apply SetoidList.InA_app_iff.
        apply SetoidList.InA_app_iff in C as [C | C]; [left | right]. { exact C. } invert C; [left | right]. { assumption. }
        apply SetoidList.InA_rev. rewrite R. right. apply SetoidList.InA_rev. assumption.
    + (* apply no_dup_app in H4 as [NDl [NDr D]]. 2: { exact Map.eq_key_equiv. } *)
      clear dec pair_dec H1 H2 H3 H4. generalize dependent r2. generalize dependent r1. generalize dependent l1.
      induction l2; intros; cbn in *. { destruct l1; invert E. { contradiction N. reflexivity. } contradiction H. left. reflexivity. }
      destruct l1; invert E; cbn in *. { contradiction H0. apply List.in_or_app. right. left. reflexivity. }
      assert (N1 : ~List.In (x2, y2) l1). { intro I. apply H. right. exact I. }
      specialize (IHl2 _ N1 _ H0 _ H3) as [l3 [r3 [-> ->]]]. do 2 eexists. split; reflexivity.
Qed.

Lemma app_cons_nil {T} (x : T) a b
  : ((a ++ x :: nil) ++ b)%list = (a ++ x :: b)%list.
Proof. generalize dependent b. induction a; intros; cbn in *. { reflexivity. } rewrite IHa. reflexivity. Qed.

Lemma app_eq_l {T} {a b x : list T} (E : (a ++ x)%list = (b ++ x)%list)
  : a = b.
Proof.
  generalize dependent b. generalize dependent a. induction x; intros; cbn in *. { repeat rewrite List.app_nil_r in E. exact E. }
  rewrite <- (app_cons_nil _ a0) in E. rewrite <- (app_cons_nil _ b) in E. specialize (IHx _ _ E). apply rev_eq in IHx.
  repeat rewrite List.rev_app_distr in IHx. cbn in IHx. invert IHx. apply rev_eq in H0. exact H0.
Qed.

Lemma count_strict_ref {context scrutinee pattern cleaved context_with_matches}
  (M : StrictRef context pattern scrutinee cleaved context_with_matches)
  : Pattern.strict_nodes_left pattern +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context_with_matches) =
    Term.nodes scrutinee +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context).
Proof.
  induction M; intros. { cbn. apply Map.bindings_eq in E as ->. reflexivity. }
  eassert (agree : _); [| assert (A' := @Map.add_overriding _ argument_name argument context_with_function_matches agree)]. {
    cbn. intros. contradiction N. eexists. exact F. } assert (E := Map.add_det A eq_refl eq_refl (Map.eq_refl _) A').
  apply Map.bindings_eq in E as ->; clear agree A'. destruct (Map.bindings_add_split N argument) as [bl [br [-> E]]].
  rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc. rewrite <- List.fold_right_app. rewrite <- E; clear bl br E.
  f_equal. repeat rewrite PeanoNat.Nat.add_assoc. repeat rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument).
  repeat rewrite <- (PeanoNat.Nat.add_assoc $ Term.nodes argument). f_equal. exact IHM.
Qed.

Lemma count_cleaved {context scrutinee pattern cleaved context_with_matches}
  (M : StrictRef context pattern scrutinee cleaved context_with_matches)
  : Term.nodes cleaved = Pattern.strict_nodes pattern.
Proof. induction M; cbn in *. { reflexivity. } f_equal. rewrite IHM. apply PeanoNat.Nat.add_1_r. Qed.

Lemma not_in_forallb {T} {li x} {y : T} (N : ~SetoidList.InA MapCore.eq_key (x, y) li)
  : List.forallb (fun kv => negb $ String.eqb x $ fst kv) li = true.
Proof.
  generalize dependent y. generalize dependent x. induction li as [| [k v] tail IH]; intros; cbn in *. { reflexivity. }
  destruct (String.eqb_spec x k); cbn in *. { subst. contradiction N. left. reflexivity. }
  eapply IH. intro I. apply N. right. exact I.
Qed.

Lemma count_strict_ref_remove {context name looked_up} (lookup : Map.Find context name looked_up)
  {scrutinee pattern cleaved context_with_matches} (M : StrictRef context pattern scrutinee cleaved context_with_matches)
  : Term.nodes looked_up +
    List.fold_right (fun kv : MapCore.key * Term.term => Nat.add $ Term.nodes $ snd kv) 0
    (MapCore.bindings $ Map.remove name context_with_matches) =
    List.fold_right (fun kv : MapCore.key * Term.term => Nat.add $ Term.nodes $ snd kv) 0
    (MapCore.bindings context_with_matches).
Proof.
  assert (F := in_strict_ref_context lookup M). apply MapCore.bindings_spec1 in F.
  apply SetoidList.InA_split in F as [bl [[k v] [br [[] E]]]]; cbn in *; subst k; subst v. rewrite E.
  assert (Er : MapCore.bindings $ Map.remove name context_with_matches = (bl ++ br)%list). {
    rewrite Map.bindings_remove. rewrite E. rewrite List.filter_app. cbn. rewrite String.eqb_refl; cbn.
    rewrite <- List.filter_app. apply List.forallb_filter_id. assert (ND := MapCore.bindings_spec2w context_with_matches).
    rewrite E in ND. apply SetoidList.NoDupA_swap in ND. 2: { exact Map.eq_key_equiv. }
    invert ND. eapply not_in_forallb. eassumption. } rewrite Er.
  rewrite (List.fold_right_app _ _ $ cons _ _). cbn. rewrite pull_out_of_acc. rewrite <- List.fold_right_app. reflexivity.
Qed.

Lemma count_strict_ref_overwrite {context name looked_up} (lookup : Map.Find context name looked_up)
  {scrutinee pattern cleaved context_with_matches} (M : StrictRef context pattern scrutinee cleaved context_with_matches)
  : Term.nodes looked_up +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0
    (MapCore.bindings $ Map.overwrite name cleaved context_with_matches) =
    Pattern.strict_nodes pattern +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0
    (MapCore.bindings context_with_matches).
Proof.
  assert (F := in_strict_ref_context lookup M). destruct (Map.bindings_overwrite_split F cleaved) as [bl [br [-> E]]].
  rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc. rewrite <- List.fold_right_app. erewrite (count_cleaved M).
  assert (E' : (bl ++ br)%list = MapCore.bindings $ Map.remove name context_with_matches). {
    rewrite Map.bindings_remove. rewrite E. rewrite List.filter_app. cbn. rewrite String.eqb_refl; cbn.
    rewrite <- List.filter_app. symmetry. apply List.forallb_filter_id. assert (ND := MapCore.bindings_spec2w context_with_matches).
    rewrite E in ND. apply SetoidList.NoDupA_swap in ND. 2: { exact Map.eq_key_equiv. }
    invert ND. eapply not_in_forallb. eassumption. } rewrite E'; clear F bl br E E'.
  rewrite PeanoNat.Nat.add_assoc. rewrite (PeanoNat.Nat.add_comm _ $ Pattern.strict_nodes _).
  rewrite <- PeanoNat.Nat.add_assoc. erewrite count_strict_ref_remove. 2: { exact lookup. } 2: { exact M. } reflexivity.
Qed.

Lemma count_strict_ref_cleaved {context name looked_up} (lookup : Map.Find context name looked_up)
  {scrutinee pattern cleaved context_with_matches} (M : StrictRef context pattern scrutinee cleaved context_with_matches)
  : S $ Term.nodes looked_up +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0
    (MapCore.bindings $ Map.overwrite name cleaved context_with_matches) =
    Pattern.strict_nodes_left pattern + Term.nodes scrutinee +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0
    (MapCore.bindings context).
Proof.
  erewrite count_strict_ref_overwrite. 2: { exact lookup. } 2: { exact M. } clear name looked_up lookup.
  induction M; intros; cbn in *. { apply Map.bindings_eq in E as ->. reflexivity. }
  f_equal. rewrite <- (PeanoNat.Nat.add_comm $ Term.nodes _). rewrite PeanoNat.Nat.add_succ_r.
  rewrite (PeanoNat.Nat.add_comm $ Term.nodes _). rewrite PeanoNat.Nat.add_assoc.
  rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument). repeat rewrite PeanoNat.Nat.add_succ_l.
  rewrite <- PeanoNat.Nat.add_assoc. rewrite <- IHM; clear IHM. rewrite PeanoNat.Nat.add_succ_r.
  rewrite PeanoNat.Nat.add_assoc. rewrite (PeanoNat.Nat.add_comm _ $ Pattern.strict_nodes _).
  repeat rewrite <- PeanoNat.Nat.add_assoc. repeat f_equal.
  destruct (Map.bindings_add_split N argument) as [bl [br [Ea Ec]]]. rewrite Ec.
  eassert (agree : _); [| assert (A' := @Map.add_overriding _ argument_name argument context_with_function_matches agree)]. {
    intros v' F'. contradiction N. eexists. exact F'. } assert (D := Map.add_det A eq_refl eq_refl (Map.eq_refl _) A').
  apply Map.bindings_eq in D as ->; clear context_with_matches A agree A'. rewrite Ea.
  rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc. rewrite <- List.fold_right_app. reflexivity.
Qed.
*)

Lemma lt_arbitrary_node a b
  : (a < S b) <-> forall t, a < b + Term.nodes t.
Proof.
  split.
  - intros L t. destruct t; cbn; try solve [rewrite PeanoNat.Nat.add_1_r; exact L];
    rewrite PeanoNat.Nat.add_succ_r; rewrite <- PeanoNat.Nat.add_succ_l; apply PeanoNat.Nat.lt_lt_add_r; exact L.
  - intro L. specialize (L $ Term.Ctr $ Constructor.Builtin Constructor.Error).
    cbn in L. rewrite PeanoNat.Nat.add_1_r in L. exact L.
Qed.

Lemma count_overwrite {original k old} (F : Map.Find original k old)
  {new overwritten} (OW : Map.OverwriteIfPresent k new original overwritten)
  : Term.nodes old + List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings overwritten) =
    Term.nodes new + List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings original).
Proof.
  destruct (Map.bindings_overwrite_split F new) as [bl [br [E' E]]]. rewrite E.
  assert (A := Map.overwrite_if_present_det OW eq_refl eq_refl (Map.eq_refl _) (Map.overwrite_if_present_overwrite _ _ _)).
  apply Map.bindings_eq in A as ->. rewrite E'. repeat rewrite List.fold_right_app. cbn. repeat rewrite pull_out_of_acc.
  repeat rewrite PeanoNat.Nat.add_assoc. f_equal. apply PeanoNat.Nat.add_comm.
Qed.

Lemma strict_ref_decreasing {context pattern scrutinee cleaved context_with_matches}
  (matched : StrictRef context pattern scrutinee cleaved context_with_matches)
  : Term.nodes cleaved +
    List.fold_right (fun kv : MapCore.key * Term.term => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context_with_matches) <
    S $ S $ Term.nodes scrutinee + Pattern.strict_nodes pattern +
    List.fold_right (fun kv : MapCore.key * Term.term => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context).
Proof.
  induction matched; cbn in *. { apply Map.bindings_eq in E as ->.
    repeat (try apply PeanoNat.Nat.lt_succ_diag_r; eapply PeanoNat.Nat.lt_trans). }
  rewrite PeanoNat.Nat.add_1_r. cbn. repeat apply -> PeanoNat.Nat.succ_lt_mono. repeat rewrite PeanoNat.Nat.add_succ_r. cbn.
  destruct (Map.bindings_add_split N argument) as [bl [br [Ea Ec]]].
  eassert (agree : _); [| assert (A' := Map.add_det A eq_refl eq_refl (Map.eq_refl _) $ Map.add_overriding agree)]. {
    intros v' F'. edestruct N. eexists. exact F'. } apply Map.bindings_eq in A' as ->; clear agree. rewrite Ea; clear Ea.
  rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc. rewrite <- List.fold_right_app. rewrite <- Ec; clear bl br Ec.
  rewrite PeanoNat.Nat.add_assoc. repeat rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes argument).
  repeat rewrite <- (PeanoNat.Nat.add_assoc $ Term.nodes argument).
  repeat rewrite <- (PeanoNat.Nat.add_succ_r $ Term.nodes argument). apply PeanoNat.Nat.add_lt_mono_l.
  eapply PeanoNat.Nat.lt_trans. { exact IHmatched. } apply PeanoNat.Nat.lt_succ_diag_r.
Qed.

Lemma move_or_reference_decreasing_simpl {context symlink name scrutinee}
  (follow_references : Context.FollowReferences context symlink name scrutinee)
  {pattern cleaved old_context_with_matches} (matched : StrictRef context pattern scrutinee cleaved old_context_with_matches)
  {context_with_matches} (OW : Map.Overwrite name cleaved old_context_with_matches context_with_matches)
  : List.fold_right
      (fun kv : MapCore.key * Term.term => Nat.add (Term.nodes (snd kv))) 0
      (MapCore.bindings context_with_matches) <
    S $ S $ Pattern.strict_nodes pattern +
    List.fold_right
      (fun kv : MapCore.key * Term.term => Nat.add (Term.nodes (snd kv))) 0
      (MapCore.bindings context).
Proof.
  assert (F := Context.follow_references_find follow_references). destruct OW as [[tmp F'] OW].
  assert (F'' := in_strict_ref_context F matched). destruct (Map.find_det F'' F'). clear F''.
  eapply PeanoNat.Nat.add_lt_mono_l. rewrite (count_overwrite F' OW). clear context_with_matches F' OW F.
  repeat rewrite PeanoNat.Nat.add_succ_r. rewrite PeanoNat.Nat.add_assoc. eapply strict_ref_decreasing; eassumption.
Qed.

Lemma move_or_reference_decreasing {context pattern scrutinee context_with_matches}
  (move_or_reference_matched : MoveOrReference context pattern scrutinee context_with_matches) other_cases
  : List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context_with_matches) <
    Pattern.move_or_reference_nodes pattern + Term.nodes other_cases + Term.nodes scrutinee +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context).
Proof.
  invert move_or_reference_matched. { apply strict_decreasing. exact S. }
  cbn. rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes other_cases). repeat rewrite <- PeanoNat.Nat.add_assoc.
  cbn. rewrite (PeanoNat.Nat.add_comm $ Term.nodes other_cases). generalize dependent other_cases. apply lt_arbitrary_node.
  rewrite PeanoNat.Nat.add_succ_r. rename S into M. eapply move_or_reference_decreasing_simpl; eassumption.
Qed.

Lemma decreasing {context pattern scrutinee context_with_matches}
  (M : Pattern context pattern scrutinee context_with_matches) other_cases
  : List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context_with_matches) <
    Pattern.nodes pattern + Term.nodes other_cases + Term.nodes scrutinee +
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 (MapCore.bindings context).
Proof.
  invert M; cbn in *. 2: { apply move_or_reference_decreasing. exact move_or_reference_matched. }
  rename S into A. eassert (agree : _); [| assert (A' := @Map.add_overriding _ name scrutinee context agree)]. {
    intros v' F'. contradiction N. eexists. exact F'. }
  eapply Map.add_det in A'; try reflexivity. 2: { exact A. } 2: { apply Map.eq_refl. }
  apply Map.bindings_eq in A' as ->. destruct (Map.bindings_add_split N scrutinee) as [bl [br [-> ->]]].
  repeat rewrite List.fold_right_app. cbn. rewrite pull_out_of_acc.
  rewrite (PeanoNat.Nat.add_comm _ $ Term.nodes scrutinee). rewrite <- PeanoNat.Nat.add_assoc. rewrite plus_n_Sm.
  apply PeanoNat.Nat.add_lt_mono_l. repeat rewrite <- PeanoNat.Nat.add_succ_l.
  apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ.
Qed.
