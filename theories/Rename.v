From LinearCore Require
  Name
  Term
  UsedIn
  .
From LinearCore Require Import
  Invert
  .



Inductive Strict (lookup : Map.to Name.name) : Pattern.strict -> Pattern.strict -> Prop :=
  | SCtr ctor
      : Strict lookup (Pattern.Ctr ctor) (Pattern.Ctr ctor)
  | SApp
      curried renamed_curried (rename_curried : Strict lookup curried renamed_curried)
      argument renamed_argument (rename_argument : Map.Find lookup argument renamed_argument)
      : Strict lookup (Pattern.App curried argument) (Pattern.App renamed_curried renamed_argument)
  .
Arguments Strict lookup strict renamed_strict.

Fixpoint strict lookup s :=
  match s with
  | Pattern.Ctr ctor => Some s
  | Pattern.App curried argument =>
      match strict lookup curried with None => None | Some renamed_curried =>
        option_map (Pattern.App renamed_curried) (Map.find lookup argument)
      end
  end.

Lemma strict_spec lookup s
  : Reflect.Option (Strict lookup s) (strict lookup s).
Proof.
  induction s; cbn in *. { constructor. constructor. }
  destruct IHs. 2: { constructor. intros t S. invert S. apply N in rename_curried as []. }
  destruct (Map.find_spec lookup argument); constructor. { constructor; assumption. }
  intros s' S. invert S. apply N in rename_argument as [].
Qed.

Lemma strict_det
  {l1 s1 r1} (S1 : Strict l1 s1 r1)
  {l2} (El : Map.Eq l1 l2)
  {s2} (Es : s1 = s2)
  {r2} (S2 : Strict l2 s2 r2)
  : r1 = r2.
Proof.
  subst. generalize dependent r2. generalize dependent l2.
  induction S1; intros; invert S2. { reflexivity. }
  f_equal. { eapply IHS1. { exact El. } exact rename_curried. }
  eapply Map.find_det; try eassumption. apply El. assumption.
Qed.



Variant MoveOrReference lookup : Pattern.move_or_reference -> Pattern.move_or_reference -> Prop :=
  | MMov strict renamed_strict (rename_strict : Strict lookup strict renamed_strict)
      : MoveOrReference lookup (Pattern.Mov strict) (Pattern.Mov renamed_strict)
  | MRef strict renamed_strict (rename_strict : Strict lookup strict renamed_strict)
      : MoveOrReference lookup (Pattern.Ref strict) (Pattern.Ref renamed_strict)
  .

Definition move_or_reference lookup mr :=
  match mr with
  | Pattern.Mov s => option_map Pattern.Mov (strict lookup s)
  | Pattern.Ref s => option_map Pattern.Ref (strict lookup s)
  end.

Lemma move_or_reference_spec lookup mr
  : Reflect.Option (MoveOrReference lookup mr) (move_or_reference lookup mr).
Proof.
  destruct mr; cbn; (destruct (strict_spec lookup strict0); constructor; [constructor; exact Y |]);
  intros s M; invert M; apply N in rename_strict as [].
Qed.

Lemma move_or_reference_det
  {l1 mr1 r1} (MR1 : MoveOrReference l1 mr1 r1)
  {l2} (El : Map.Eq l1 l2)
  {mr2} (Emr : mr1 = mr2)
  {r2} (MR2 : MoveOrReference l2 mr2 r2)
  : r1 = r2.
Proof. invert MR1; invert MR2; f_equal; eapply strict_det; try reflexivity; eassumption. Qed.



Variant Pattern lookup : Pattern.pattern -> Pattern.pattern -> Prop :=
  | Nam name renamed (rename_name : Map.Find lookup name renamed)
      : Pattern lookup (Pattern.Nam name) (Pattern.Nam renamed)
  | Pat move_or_reference renamed_move_or_reference
      (rename_move_or_reference : MoveOrReference lookup move_or_reference renamed_move_or_reference)
      : Pattern lookup (Pattern.Pat move_or_reference) (Pattern.Pat renamed_move_or_reference)
  .

Definition pattern lookup p :=
  match p with
  | Pattern.Nam name => option_map Pattern.Nam (Map.find lookup name)
  | Pattern.Pat mr => option_map Pattern.Pat (move_or_reference lookup mr)
  end.

Lemma pattern_spec lookup p
  : Reflect.Option (Pattern lookup p) (pattern lookup p).
Proof.
  destruct p; cbn in *.
  - destruct (Map.find_spec lookup name); constructor. { constructor. exact Y. }
    intros p P. invert P. apply N in rename_name as [].
  - destruct (move_or_reference_spec lookup move_or_reference0); constructor. { constructor. exact Y. }
    intros p P. invert P. apply N in rename_move_or_reference as [].
Qed.

Lemma pattern_det
  {l1 p1 r1} (P1 : Pattern l1 p1 r1)
  {l2} (El : Map.Eq l1 l2)
  {p2} (Ep : p1 = p2)
  {r2} (P2 : Pattern l2 p2 r2)
  : r1 = r2.
Proof.
  invert P1; invert P2; f_equal. { eapply Map.find_det. { eassumption. } apply El. assumption. }
  eapply move_or_reference_det; try reflexivity; eassumption.
Qed.



Inductive Term (lookup : Map.to Name.name) : Term.term -> Term.term -> Prop :=
  | Err
      : Term lookup Term.Err Term.Err
  | Typ
      : Term lookup Term.Typ Term.Typ
  | Prp
      : Term lookup Term.Prp Term.Prp
  | Ctr ctor
      : Term lookup (Term.Ctr ctor) (Term.Ctr ctor) (* constructor names live in a different universe *)
  | Mov x y (F : Map.Find lookup x y)
      : Term lookup (Term.Mov x) (Term.Mov y)
  | Ref x y (F : Map.Find lookup x y)
      : Term lookup (Term.Ref x) (Term.Ref y)
  | App
      function renamed_function (function_renaming : Term lookup function renamed_function)
      argument renamed_argument (argument_renaming : Term lookup argument renamed_argument)
      : Term lookup (Term.App function argument) (Term.App renamed_function renamed_argument)
  | For
      type renamed_type (type_renaming : Term lookup type renamed_type)
      variable unshadowed (not_shadowed : Map.OverwriteIfPresent variable variable lookup unshadowed)
      body renamed_body (body_renaming : Term unshadowed body renamed_body)
      : Term lookup (Term.For variable type body) (Term.For variable renamed_type renamed_body)
  | Cas
      other_cases renamed_other_cases (other_cases_renaming : Term lookup other_cases renamed_other_cases)
      pattern bound_in_pattern (find_pattern_bindings : Map.Reflect (BoundIn.Pattern pattern) bound_in_pattern)
      pattern_to_self (pattern_idem : Map.ToSelf bound_in_pattern pattern_to_self)
      unshadowed (not_shadowed : Map.BulkOverwrite pattern_to_self lookup unshadowed)
      body_if_match renamed_body_if_match (body_if_match_renaming : Term unshadowed body_if_match renamed_body_if_match)
      : Term lookup
        (Term.Cas pattern body_if_match other_cases)
        (Term.Cas pattern renamed_body_if_match renamed_other_cases)
  .
Arguments Term lookup term renamed.



Lemma eq {l1 t1 y1} (R1 : Term l1 t1 y1)
  {l2} (El : Map.Eq l1 l2)
  {t2} (Et : t1 = t2)
  {y2} (Ey : y1 = y2)
  : Term l2 t2 y2.
Proof.
  subst. rename t2 into t. rename y2 into y. generalize dependent l2. induction R1; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply El. exact F.
  - constructor. apply El. exact F.
  - constructor; [apply IHR1_1 | apply IHR1_2]; exact El.
  - econstructor. { apply IHR1_1. exact El. } 2: { exact R1_2. }
    eapply Map.overwrite_if_present_eq; try reflexivity; try eassumption. apply Map.eq_refl.
  - econstructor; try eassumption. { apply IHR1_1. exact El. }
    eapply Map.bulk_overwrite_eq; try eassumption; apply Map.eq_refl.
Qed.



(* TODO: Grammar: should this have an `e`? I'm leaning toward yes. *)
Definition RenameableTerm (lookup : Map.to Name.name) term : Prop :=
  forall x (U : UsedIn.Term term x), Map.In lookup x.
Arguments RenameableTerm lookup term/.

Lemma renameable_term lookup term :
  (exists renamed, Term lookup term renamed) <-> RenameableTerm lookup term.
Proof.
  cbn. split.
  - intros [renamed R]; intros. induction R.
    + invert U.
    + invert U.
    + invert U.
    + invert U.
    + invert U. eexists. exact F.
    + invert U. eexists. exact F.
    + invert U; [apply IHR1 | apply IHR2]; assumption.
    + invert U. { apply IHR1. assumption. } specialize (IHR2 used_in_body) as [y IH].
      apply not_shadowed in IH as [[-> ->] | [N F]]. { contradiction not_shadowed0. reflexivity. } eexists. exact F.
    + invert U. 2: { apply IHR1. exact used_in_another_case. } specialize (IHR2 used_in_body) as [y IH].
      apply not_shadowed in IH as [F | [N F]]. 2: { eexists. exact F. }
      apply pattern_idem in F as [I ->]. apply find_pattern_bindings in I. apply not_shadowed0 in I as [].
  - intros I. generalize dependent lookup. induction term; intros.
    + eexists. constructor.
    + eexists. constructor.
    + eexists. constructor.
    + eexists. constructor.
    + edestruct I as [y F]. { constructor. } eexists. constructor. exact F.
    + edestruct I as [y F]. { constructor. } eexists. constructor. exact F.
    + edestruct IHterm1 as [rf IHf]. { intros. apply I. apply UsedIn.ApF. exact U. }
      edestruct IHterm2 as [ra IHa]. { intros. apply I. apply UsedIn.ApA. exact U. }
      eexists. constructor; [exact IHf | exact IHa].
    + edestruct IHterm1 as [rt IHt]. { intros. apply I. apply UsedIn.FoT. exact U. }
      edestruct IHterm2 as [rb IHb]. 2: {
        eexists. econstructor; try eassumption. apply Map.overwrite_if_present_overwrite. }
      intros. eapply Map.in_overwrite_if_present. { apply Map.overwrite_if_present_overwrite. }
      destruct (Name.spec x variable); [left | right]. { exact Y. } apply I. apply UsedIn.FoB; assumption.
    + edestruct IHterm2 as [ro IHo]. { intros. apply I. apply UsedIn.CaO. exact U. }
      edestruct IHterm1 as [rb IHb]. 2: {
        eexists. econstructor; try eassumption. { apply BoundIn.pattern_spec. } { apply Map.to_self_to_self. }
        apply Map.bulk_overwrite_bulk_overwrite. }
      intros. eapply Map.in_bulk_overwrite. { apply Map.bulk_overwrite_bulk_overwrite. }
      rewrite Map.in_to_self. destruct (Map.in_spec (BoundIn.pattern pattern0) x); [left | right]. { exact Y. }
      split. { exact N. } apply I. apply UsedIn.CaB. 2: { exact U. }
      intro B. apply N. apply BoundIn.pattern_spec. exact B.
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

Lemma term_spec lookup t
  : Reflect.Option (Term lookup t) (term lookup t).
Proof.
  generalize dependent lookup. induction t; intros; cbn in *; try solve [repeat constructor].
  - destruct (Map.find_spec lookup name); constructor. { constructor. exact Y. }
    intros t C. invert C. apply N in F as [].
  - destruct (Map.find_spec lookup name); constructor. { constructor. exact Y. }
    intros t C. invert C. apply N in F as [].
  - destruct (IHt1 lookup). 2: { constructor. intros t C. invert C. apply N in function_renaming as []. }
    destruct (IHt2 lookup); constructor. { constructor; assumption. }
    intros t C. invert C. apply N in argument_renaming as [].
  - destruct (IHt1 lookup). 2: { constructor. intros t C. invert C. apply N in type_renaming as []. }
    destruct (IHt2 (Map.overriding_add variable variable lookup)); constructor. {
      econstructor; try eassumption. apply Map.overwrite_if_present_overwrite. }
    intros t C. invert C. eapply N. eapply eq; try reflexivity; try eassumption.
    eapply Map.overwrite_if_present_det; try reflexivity; try eassumption. { apply Map.eq_refl. }
    apply Map.overwrite_if_present_overwrite.
  - destruct (IHt2 lookup). 2: { constructor. intros t C. invert C. apply N in other_cases_renaming as []. }
    fold (Map.to_self (BoundIn.pattern pattern0)).
    destruct (IHt1 (Map.overriding_union (Map.to_self (BoundIn.pattern pattern0)) lookup)); constructor. {
      econstructor; try eassumption. { apply BoundIn.pattern_spec. } { apply Map.to_self_to_self. }
      apply Map.bulk_overwrite_bulk_overwrite. }
    intros t R. invert R. eapply N. eapply eq; try reflexivity. { exact body_if_match_renaming. }
    eapply Map.bulk_overwrite_det. { exact not_shadowed. } 3: { apply Map.bulk_overwrite_bulk_overwrite. }
    2: { apply Map.eq_refl. } eapply Map.to_self_det; try eassumption. 2: { apply Map.to_self_to_self. }
    intros x' y'. split; intro F; (eassert (I : Map.In _ _); [eexists; exact F |]).
    + eapply find_pattern_bindings in I. apply BoundIn.pattern_spec in I. destruct I as [[] I]. destruct y'. exact I.
    + apply BoundIn.pattern_spec in I. apply find_pattern_bindings in I. destruct I as [[] I]. destruct y'. exact I.
Qed.

Lemma term_det
  {l1 t1 r1} (T1 : Term l1 t1 r1)
  {l2} (El : Map.Eq l1 l2)
  {t2} (Et : t1 = t2)
  {r2} (T2 : Term l2 t2 r2)
  : r1 = r2.
Proof.
  subst. generalize dependent r2. generalize dependent l2. induction T1; intros; invert T2; try reflexivity.
  - f_equal. eapply Map.find_det. { eassumption. } apply El. assumption.
  - f_equal. eapply Map.find_det. { eassumption. } apply El. assumption.
  - f_equal; [eapply IHT1_1 | eapply IHT1_2]; eassumption.
  - f_equal. { eapply IHT1_1; eassumption. } eapply IHT1_2. 2: { eassumption. }
    eapply Map.overwrite_if_present_det; try reflexivity; eassumption.
  - f_equal. 2: { eapply IHT1_1; eassumption. } eapply IHT1_2. 2: { eassumption. }
    eapply Map.bulk_overwrite_det; try reflexivity; try eassumption.
    eapply Map.to_self_det; try eassumption. intros x [].
    split; intro F; (eassert (I : Map.In _ _); [eexists; exact F |]);
    [apply find_pattern_bindings in I | apply find_pattern_bindings0 in I];
    [apply find_pattern_bindings0 in I | apply find_pattern_bindings in I];
    destruct I as [[] F']; exact F'.
Qed.
