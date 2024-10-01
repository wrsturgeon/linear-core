From LinearCore Require
  BoundIn
  Context
  Map
  Pattern
  Term
  Unshadow
  WellFormed
  .
From LinearCore Require Import
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
        (Term.App function_cleaved (Term.Mov argument_name))
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
              Some (Term.App function_cleaved (Term.Mov argument_name), context_with_matches)
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
  | Ref
      name scrutinee (lookup : Map.Find context name scrutinee)
      strict old_context_with_matches cleaved (S : StrictRef context strict scrutinee cleaved old_context_with_matches)
      context_with_matches (OW : Map.Overwrite name cleaved old_context_with_matches context_with_matches)
      : MoveOrReference context (Pattern.Ref strict) (Term.Ref name) context_with_matches
  .
Arguments MoveOrReference context strict scrutinee context_with_matches.

Example match_referenced_application ctor arg argn name (N : argn <> name)
  : let pattern := Pattern.Ref (Pattern.App (Pattern.Ctr ctor) argn) in
    let scrutinee := Term.App (Term.Ctr ctor) arg in
    let context := Map.overriding_add name scrutinee Map.empty in
    let context_with_matches :=
      (* Note how each right-hand branch is turned into a `Mov` referencing the contents of the branch: *)
      Map.overriding_add name (Term.App (Term.Ctr ctor) (Term.Mov argn)) (
      Map.overriding_add argn arg (
      Map.empty)) in
    MoveOrReference context pattern (Term.Ref name) context_with_matches.
Proof.
  cbn. econstructor.
  - apply Map.find_overriding_add. left. split; reflexivity.
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
      Map.overriding_add name (Term.App (Term.App (Term.Ctr ctor) (Term.Mov arg1n)) (Term.Mov arg2n)) (
      Map.overriding_add arg1n arg1 (
      Map.overriding_add arg2n arg2 (
      Map.empty))) in
    MoveOrReference context pattern (Term.Ref name) context_with_matches.
Proof.
  cbn. econstructor.
  - apply Map.find_overriding_add. left. split; reflexivity.
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
  | Pattern.Mov s => strict context s scrutinee
  | Pattern.Ref s =>
      match scrutinee with
      | Term.Ref name =>
          match Map.find context name with
          | None => None
          | Some term =>
              match strict_ref context s term with
              | None => None
              | Some (cleaved, context_with_matches) =>
                  Some (Map.overwrite name cleaved context_with_matches)
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
  subst. invert S1; invert S2.
  - eapply strict_det; try reflexivity; eassumption.
  - apply Ec in lookup0. edestruct (Map.find_det lookup lookup0).
    destruct (strict_ref_det S Ec eq_refl eq_refl S0) as [<- Eoc].
    eapply Map.overwrite_det; try reflexivity; eassumption.
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
  - econstructor. { apply Ec. exact lookup. }
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
  - destruct scrutinee; try (constructor; intros m C; invert C).
    destruct (Map.find_spec context name). 2: { constructor. intros m C. invert C. apply N in lookup as []. }
    destruct (strict_ref_spec context strict0 x). 2: {
      constructor. intros m C. invert C. destruct (Map.find_det Y lookup). apply (N (_, _)) in S as []. }
    destruct x0 as [t ctx]; cbn in *. constructor. econstructor; try eassumption.
    apply Map.overwrite_overwrite. eapply in_strict_ref. { exact Y0. } right. eexists. exact Y.
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



Lemma unshadow_strict {scrutinee} (Ut : Unshadow.Unshadowed scrutinee)
  {context} (Uc : Map.ForAll (fun _ => Unshadow.Unshadowed) context)
  {pattern context_with_matches} (M : Strict context pattern scrutinee context_with_matches)
  : Map.ForAll (fun _ => Unshadow.Unshadowed) context_with_matches.
Proof.
  cbn. generalize dependent Uc. generalize dependent Ut. induction M; intros. { eapply Uc. apply E. exact F. }
  invert Ut. apply A in F as [[-> ->] | F]. { exact Ua. } eapply IHM; eassumption.
Qed.

Lemma unshadow_strict_ref {scrutinee} (Ut : Unshadow.Unshadowed scrutinee)
  {context} (Uc : Map.ForAll (fun _ => Unshadow.Unshadowed) context)
  {pattern cleaved context_with_matches} (M : StrictRef context pattern scrutinee cleaved context_with_matches)
  : Unshadow.Unshadowed cleaved /\ Map.ForAll (fun _ => Unshadow.Unshadowed) context_with_matches.
Proof.
  cbn. generalize dependent Uc. generalize dependent Ut. induction M; intros.
  - split. { constructor. } intros. eapply Uc. apply E. exact F.
  - invert Ut. specialize (IHM Uf Uc) as [IHt IHc]. split.
    + constructor; intros. { exact IHt. } { constructor. } 2: { invert Ba. }
      eapply not_bound_in_cleaved in Bf as []. exact M.
    + intros. apply A in F as [[-> ->] | F]. { exact Ua. } eapply IHc; eassumption.
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
    + eapply Uc. exact lookup.
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
