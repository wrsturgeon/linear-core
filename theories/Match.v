From LinearCore Require
  BoundIn
  Context
  Map
  Pattern
  Term
  .
From LinearCore Require Import
  Invert
  .



Inductive Strict (context : Context.context) : Pattern.strict -> Term.term -> Context.context -> Prop :=
  | Ctr context_with_matches (E : Map.Eq context context_with_matches) ctor
      : Strict context (Pattern.Ctr ctor) (Term.Ctr ctor) context_with_matches
  | App function_pattern function
      context_with_function_matches (function_matched :
        Strict context function_pattern function context_with_function_matches)
      argument_name (N : forall (I : Map.In context_with_function_matches argument_name), False)
      (* can't match the same name twice in the same pattern ^^^ *)
      argument context_with_matches (A :
        Map.Add argument_name argument context_with_function_matches context_with_matches)
      : Strict context (Pattern.App function_pattern argument_name) (Term.App function argument) context_with_matches
  .
Arguments Strict context strict term context_with_matches.

Fixpoint strict context pattern term : option Context.context :=
  match pattern, term with
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

Lemma strict_spec context pattern term
  : Reflect.Option (Strict context pattern term) (strict context pattern term).
Proof.
  generalize dependent term. induction pattern; intros;
  destruct term; try solve [constructor; intros t C; invert C].
  - unfold strict. destruct (Constructor.eq_spec constructor constructor0); constructor.
    + subst. constructor. apply Map.eq_refl.
    + intros t C. invert C. apply N. reflexivity.
  - simpl strict. destruct (IHpattern term1) as [function_matches function_matched | N]. 2: {
      constructor. intros t C. invert C. apply N in function_matched as []. }
    destruct (Map.find_spec function_matches argument) as [duplicated F | N]. 2: {
      constructor. econstructor. { eassumption. } { intros [y F]. apply N in F as []. }
      apply Map.add_overriding. cbn. intros. apply N in F as []. }
    constructor. intros t C. invert C. apply N; clear N. eexists.
    eapply strict_det; try reflexivity; [eassumption | | | eassumption];
    try eassumption. apply Map.eq_refl.
Qed.

Lemma in_strict {context strict term context_with_matches} (S : Strict context strict term context_with_matches) x
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



Inductive StrictRef (context : Context.context) : Pattern.strict -> Term.term -> Term.term -> Context.context -> Prop :=
  | CtrR context_with_matches (E : Map.Eq context context_with_matches) ctor
      : StrictRef context (Pattern.Ctr ctor) (Term.Ctr ctor) (Term.Ctr ctor) context_with_matches
  | AppR
      function_pattern function context_with_function_matches function_cleaved (function_matched :
        StrictRef context function_pattern function function_cleaved context_with_function_matches)
      argument_name (N : forall (I : Map.In context_with_function_matches argument_name), False)
      (* can't match the same name twice in the same pattern ^^^ *)
      argument context_with_matches (A :
        Map.Add argument_name argument context_with_function_matches context_with_matches)
      : StrictRef context
        (Pattern.App function_pattern argument_name)
        (Term.App function argument)
        (Term.App function_cleaved (Term.Mov argument_name))
        context_with_matches
  .
Arguments StrictRef context strict term cleaved context_with_matches.

Fixpoint strict_ref context pattern term : option (Term.term * Context.context) :=
  match pattern, term with
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

Lemma strict_ref_spec context pattern term
  : Reflect.Option (fun pair => StrictRef context pattern term (fst pair) (snd pair)) (strict_ref context pattern term).
Proof.
  generalize dependent term. induction pattern; intros;
  destruct term; try solve [constructor; intros t C; invert C].
  - unfold strict_ref. destruct (Constructor.eq_spec constructor constructor0); constructor.
    + subst. constructor. apply Map.eq_refl.
    + intros t C. invert C. apply N. reflexivity.
  - simpl strict_ref. destruct (IHpattern term1) as [[cleaved function_matches] function_matched | N]. 2: {
      constructor. intros t C. invert C. apply (N (_, _)) in function_matched as []. }
    destruct (Map.find_spec function_matches argument) as [duplicated F | N]. 2: {
      constructor. econstructor. { eassumption. } { intros [y F]. apply N in F as []. }
      apply Map.add_overriding. cbn. intros. apply N in F as []. }
    constructor. intros t C. invert C. apply N; clear N. eexists.
    eapply strict_ref_det; try reflexivity; [eassumption | | | eassumption];
    try eassumption. apply Map.eq_refl.
Qed.

Lemma in_strict_ref {context strict term cleaved context_with_matches}
  (S : StrictRef context strict term cleaved context_with_matches) x
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



Variant MoveOrReference (context : Context.context) : Pattern.move_or_reference -> Term.term -> Context.context -> Prop :=
  | Mov strict term context_with_matches (S : Strict context strict term context_with_matches)
      : MoveOrReference context (Pattern.Mov strict) term context_with_matches
  | Ref
      name term (lookup : Map.Find context name term)
      strict old_context_with_matches cleaved (S : StrictRef context strict term cleaved old_context_with_matches)
      context_with_matches (OW : Map.Overwrite name cleaved old_context_with_matches context_with_matches)
      : MoveOrReference context (Pattern.Ref strict) (Term.Ref name) context_with_matches
  .
Arguments MoveOrReference context strict term context_with_matches.

Example match_referenced_application ctor arg argn name (N : argn <> name)
  : let pattern := Pattern.Ref (Pattern.App (Pattern.Ctr ctor) argn) in
    let term := Term.App (Term.Ctr ctor) arg in
    let context := Map.overriding_add name term Map.empty in
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
    let term := Term.App (Term.App (Term.Ctr ctor) arg1) arg2 in
    let context := Map.overriding_add name term Map.empty in
    let context_with_matches := (* Note how each right-hand branch is turned into a `Mov` referencing the contents of the branch: *)
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

Definition move_or_reference context pattern term :=
  match pattern with
  | Pattern.Mov s => strict context s term
  | Pattern.Ref s =>
      match term with
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

Lemma in_move_or_reference {context move_or_reference term context_with_matches}
  (MR : MoveOrReference context move_or_reference term context_with_matches) x
  : Map.In context_with_matches x <-> (BoundIn.MoveOrReference move_or_reference x \/ Map.In context x).
Proof.
  invert MR.
  - erewrite in_strict. 2: { exact S. } split; (intros [B | I]; [left | right; exact I]). { constructor. exact B. }
    invert B. exact bound_in_strict.
  - erewrite Map.in_overwrite. 2: { exact OW. } erewrite in_strict_ref. 2: { exact S. }
    split; (intros [B | I]; [left | right; exact I]). { constructor. exact B. } invert B. exact bound_in_strict.
Qed.

Lemma move_or_reference_spec context pattern term
  : Reflect.Option (MoveOrReference context pattern term) (move_or_reference context pattern term).
Proof.
  destruct pattern; cbn.
  - cbn. destruct (strict_spec context strict0 term); constructor. { constructor. exact Y. }
    intros x MR. invert MR. apply N in S as [].
  - destruct term; try (constructor; intros m C; invert C).
    destruct (Map.find_spec context name). 2: { constructor. intros m C. invert C. apply N in lookup as []. }
    destruct (strict_ref_spec context strict0 x). 2: {
      constructor. intros m C. invert C. destruct (Map.find_det Y lookup). apply (N (_, _)) in S as []. }
    destruct x0 as [t ctx]; cbn in *. constructor. econstructor; try eassumption.
    apply Map.overwrite_overwrite. eapply in_strict_ref. { exact Y0. } right. eexists. exact Y.
Qed.



Variant Pattern (context : Context.context) : Pattern.pattern -> Term.term -> Context.context -> Prop :=
  | Nam
      name (N : forall (I : Map.In context name), False)
      term context_with_matches (S : Map.Add name term context context_with_matches)
      : Pattern context (Pattern.Nam name) term context_with_matches
  | Pat
      move_or_reference term context_with_matches (move_or_reference_matched :
        MoveOrReference context move_or_reference term context_with_matches)
      : Pattern context (Pattern.Pat move_or_reference) term context_with_matches
  .
Arguments Pattern context pattern term context_with_matches.

Definition pattern context patt term :=
  match patt with
  | Pattern.Nam name => Map.disjoint_add name term context
  | Pattern.Pat mor => move_or_reference context mor term
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

Lemma pattern_spec context patt term
  : Reflect.Option (Pattern context patt term) (pattern context patt term).
Proof.
  destruct patt; cbn.
  - destruct (Map.find_spec context name); constructor. { intros m C. invert C. apply N. eexists. exact Y. }
    constructor. { intros [y F]. eapply N. exact F. } apply Map.add_overriding. cbn. intros. apply N in F as [].
  - destruct (move_or_reference_spec context move_or_reference0 term); constructor. { constructor. exact Y. }
    intros ctx C. invert C. apply N in move_or_reference_matched as [].
Qed.
