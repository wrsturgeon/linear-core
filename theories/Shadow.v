From LinearCore Require
  BoundIn
  NewNames
  Rename
  Term
  UsedIn
  .
From LinearCore Require Import
  Invert
  .



Inductive Anywhere : Term.term -> Prop :=
  | AppF {function} (deeper_in_function : Anywhere function) argument
      : Anywhere (Term.App function argument)
  | AppA {argument} (deeper_in_argument : Anywhere argument) function
      : Anywhere (Term.App function argument)
  | AppFA {function x} (bound_in_function : BoundIn.Term function x) {argument} (used_in_argument : UsedIn.Term argument x)
      : Anywhere (Term.App function argument)
  | AppAF {argument x} (bound_in_argument : BoundIn.Term argument x) {function} (used_in_function : UsedIn.Term function x)
      : Anywhere (Term.App function argument)
  | ForT {type} (deeper_in_type : Anywhere type) variable body
      : Anywhere (Term.For variable type body)
  | ForB {body} (deeper_in_body : Anywhere body) variable type
      : Anywhere (Term.For variable type body)
  | ForTB {type x} (bound_in_type : BoundIn.Term type x) {body} (used_in_body : UsedIn.Term body x) variable
      : Anywhere (Term.For variable type body)
  | ForBT {body x} (bound_in_body : BoundIn.Term body x) {type} (used_in_type : UsedIn.Term type x) variable
      : Anywhere (Term.For variable type body)
  | ForVB {variable body} (rebound_in_body : BoundIn.Term body variable) type
      : Anywhere (Term.For variable type body)
  | CasB {body_if_match} (deeper_in_body_if_match : Anywhere body_if_match) pattern other_cases
      : Anywhere (Term.Cas pattern body_if_match other_cases)
  | CasO {other_cases} (deeper_in_other_cases : Anywhere other_cases) pattern body_if_match
      : Anywhere (Term.Cas pattern body_if_match other_cases)
  | CasBO {body_if_match x} (bound_in_body_if_match : BoundIn.Term body_if_match x)
      {other_cases} (used_in_other_cases : UsedIn.Term other_cases x) pattern
      : Anywhere (Term.Cas pattern body_if_match other_cases)
  | CasOB {other_cases x} (bound_in_other_cases : BoundIn.Term other_cases x)
      {body_if_match} (used_in_body_if_match : UsedIn.Term body_if_match x) pattern
      : Anywhere (Term.Cas pattern body_if_match other_cases)
  | CasPB {pattern x} (bound_in_pattern : BoundIn.Pattern pattern x)
      {body_if_match} (rebound_in_body_if_match : BoundIn.Term body_if_match x) other_cases
      : Anywhere (Term.Cas pattern body_if_match other_cases)
  .



Fixpoint fast_check t : option (Map.set * Map.set) :=
  match t with
  | Term.Mov name
  | Term.Ref name => Some (Map.empty, Map.singleton name tt)
  | Term.App function argument =>
      match fast_check function with None => None | Some (bound_in_function, used_in_function) =>
        match fast_check argument with None => None | Some (bound_in_argument, used_in_argument) =>
          if Map.disjoint bound_in_function used_in_argument then
            if Map.disjoint bound_in_argument used_in_function then
              Some (Map.overriding_union bound_in_function bound_in_argument, Map.overriding_union used_in_argument used_in_function)
            else None
          else None
        end
      end
  | Term.For variable type body =>
      match fast_check type with None => None | Some (bound_in_type, used_in_type) =>
        match fast_check body with None => None | Some (bound_in_body, used_in_body) =>
          if Map.in_ bound_in_body variable then
            None
          else
            if Map.disjoint bound_in_type used_in_body then
              if Map.disjoint bound_in_body used_in_type then Some (
                Map.overriding_add variable tt (Map.overriding_union bound_in_type bound_in_body),
                Map.overriding_union used_in_type (Map.remove variable used_in_body)
              ) else None
            else None
        end
      end
  | Term.Cas pattern body_if_match other_cases =>
      match fast_check body_if_match with None => None | Some (bound_in_body_if_match, used_in_body_if_match) =>
        match fast_check other_cases with None => None | Some (bound_in_other_cases, used_in_other_cases) =>
          let bound_in_pattern := BoundIn.pattern pattern in
          if Map.disjoint bound_in_body_if_match bound_in_pattern then
            if Map.disjoint bound_in_other_cases used_in_body_if_match then
              if Map.disjoint bound_in_body_if_match used_in_other_cases then Some (
                Map.overriding_union bound_in_pattern (Map.overriding_union bound_in_other_cases bound_in_body_if_match),
                Map.overriding_union used_in_other_cases (Map.minus used_in_body_if_match bound_in_pattern)
              ) else None
            else None
          else None
        end
      end
  | _ => Some (Map.empty, Map.empty)
  end.

Lemma fast_check_bound_used t bound used (E : fast_check t = Some (bound, used))
  : Map.Reflect (BoundIn.Term t) bound /\ Map.Reflect (UsedIn.Term t) used.
Proof.
  generalize dependent used. generalize dependent bound. induction t; intros; simpl fast_check in *;
  try solve [invert E; split; (split; [intro I; apply Map.empty_empty in I as [] | intro B; invert B])].
  - invert E. split. { split. { intro I. apply Map.empty_empty in I as []. } intro B. invert B. }
    split. { intro I. apply Map.in_singleton in I as ->. constructor. }
    intro U. invert U. apply Map.in_singleton. reflexivity.
  - invert E. split. { split. { intro I. apply Map.empty_empty in I as []. } intro B. invert B. }
    split. { intro I. apply Map.in_singleton in I as ->. constructor. }
    intro U. invert U. apply Map.in_singleton. reflexivity.
  - destruct (fast_check t1) as [[bound_in_function used_in_function] |]. 2: { discriminate E. }
    destruct (fast_check t2) as [[bound_in_argument used_in_argument] |]. 2: { discriminate E. }
    specialize (IHt1 _ _ eq_refl) as [Bf Uf]. specialize (IHt2 _ _ eq_refl) as [Ba Ua].
    assert (D := @Map.disjoint_spec). cbn in D.
    destruct (D _ _ bound_in_function used_in_argument); simpl in E. 2: { discriminate E. }
    destruct (D _ _ bound_in_argument used_in_function); invert E. clear D. split.
    + split. 2: { intro B. apply Map.in_overriding_union. invert B; [left | right]; [apply Bf | apply Ba]; assumption. }
      intro I. apply Map.in_overriding_union in I as [I | I]. { apply BoundIn.TApF. apply Bf. exact I. }
      apply BoundIn.TApA. apply Ba. exact I.
    + split. 2: { intro U. apply Map.in_overriding_union. invert U; [right | left]; [apply Uf | apply Ua]; assumption. }
      intro I. apply Map.in_overriding_union in I as [I | I]. { apply UsedIn.ApA. apply Ua. exact I. }
      apply UsedIn.ApF. apply Uf. exact I.
  - destruct (fast_check t1) as [[bound_in_type used_in_type] |]. 2: { discriminate E. }
    destruct (fast_check t2) as [[bound_in_body used_in_body] |]. 2: { discriminate E. }
    specialize (IHt1 _ _ eq_refl) as [Bt Ut]. specialize (IHt2 _ _ eq_refl) as [Bb Ub].
    destruct (Map.find_spec bound_in_body variable). { discriminate E. }
    assert (D := @Map.disjoint_spec). cbn in D.
    destruct (D _ _ bound_in_type used_in_body); simpl in E. 2: { discriminate E. }
    destruct (D _ _ bound_in_body used_in_type); invert E. clear D. split.
    + split. 2: { intro B. apply Map.in_overriding_add. rewrite Map.in_overriding_union.
        invert B. { left. reflexivity. } { right. left. apply Bt. assumption. } right. right. apply Bb. assumption. }
      intro I. apply Map.in_overriding_add in I as [-> | I]; [| apply Map.in_overriding_union in I as [I | I]].
      * apply BoundIn.TFoV.
      * apply BoundIn.TFoT. apply Bt. exact I.
      * apply BoundIn.TFoB. apply Bb. exact I.
    + split. 2: { intro U. apply Map.in_overriding_union. invert U; [left | right]. { apply Ut. assumption. }
        eapply Map.in_remove_if_present. { apply Map.remove_if_present_remove. }
        split. { assumption. } apply Ub. assumption. }
      intro I. apply Map.in_overriding_union in I as [I | I]; [| eapply Map.in_remove_if_present in I as [Nx I]]. 3: {
        apply Map.remove_if_present_remove. } { apply UsedIn.FoT. apply Ut. exact I. }
      apply UsedIn.FoB. { exact Nx. } apply Ub. exact I.
  - destruct (fast_check t1) as [[bound_in_body_if_match used_in_body_if_match] |]. 2: { discriminate E. }
    destruct (fast_check t2) as [[bound_in_other_cases used_in_other_cases] |]. 2: { discriminate E. }
    specialize (IHt1 _ _ eq_refl) as [Bb Ub]. specialize (IHt2 _ _ eq_refl) as [Bo Uo].
    assert (D := @Map.disjoint_spec). cbn in D.
    destruct (D _ _ bound_in_body_if_match (BoundIn.pattern pattern)). 2: { discriminate E. }
    destruct (D _ _ bound_in_other_cases used_in_body_if_match); simpl in E. 2: { discriminate E. }
    destruct (D _ _ bound_in_body_if_match used_in_other_cases); invert E. clear D. split.
    + split. 2: { intro B. apply Map.in_overriding_union. rewrite Map.in_overriding_union.
        assert (A := BoundIn.pattern_spec). unfold BoundIn.Reflect in A. unfold Map.Reflect in A. rewrite A. clear A.
        invert B. { left. assumption. } { right. right. apply Bb. assumption. } right. left. apply Bo. assumption. }
      intro I. apply Map.in_overriding_union in I as [I | I]; [| apply Map.in_overriding_union in I as [I | I]].
      * apply BoundIn.TCaP. apply BoundIn.pattern_spec. exact I.
      * apply BoundIn.TCaO. apply Bo. exact I.
      * apply BoundIn.TCaB. apply Bb. exact I.
    + split. 2: { intro U. apply Map.in_overriding_union. invert U; [right | left]. 2: { apply Uo. assumption. }
        exists tt. apply Map.minus_minus. split. { apply Ub in used_in_body as [[] Ub']. exact Ub'. }
        intro B. apply not_shadowed. apply BoundIn.pattern_spec. exact B. }
      intro I. apply Map.in_overriding_union in I as [I | I]. { apply UsedIn.CaO. apply Uo. exact I. }
      destruct I as [[] F]. apply Map.minus_minus in F as [F N]. apply UsedIn.CaB. 2: { apply Ub. exists tt. exact F. }
      intro B. apply N. apply BoundIn.pattern_spec. exact B.
Qed.

Definition anywhere t := match fast_check t with None => true | Some _ => false end.
Arguments anywhere t/.

Lemma anywhere_spec t
  : Reflect.Bool (Anywhere t) (anywhere t).
Proof.
  induction t; cbn in *; try solve [constructor; intro C; invert C].
  - destruct (fast_check t1) as [[bf uf] |] eqn:Ef; invert IHt1. 2: { constructor. eapply AppF. exact Y. }
    destruct (fast_check t2) as [[ba ua] |] eqn:Ea; invert IHt2. 2: { constructor. eapply AppA. exact Y. }
    apply fast_check_bound_used in Ef as [Bf Uf]. apply fast_check_bound_used in Ea as [Ba Ua].
    assert (D := @Map.disjoint_spec). cbn in D.
    destruct (D _ _ bf ua). 2: { constructor.
      apply Map.not_disjoint_exists in N1 as [k [Bfk Uak]]. eapply AppFA; [apply Bf | apply Ua]; eassumption. }
    destruct (D _ _ ba uf). 2: { constructor.
      apply Map.not_disjoint_exists in N1 as [k [Bak Ufk]]. eapply AppAF; [apply Ba | apply Uf]; eassumption. }
    constructor. intro C. invert C.
    + apply N in deeper_in_function as [].
    + apply N0 in deeper_in_argument as [].
    + eapply Y; [apply Bf | apply Ua]; eassumption.
    + eapply Y0; [apply Ba | apply Uf]; eassumption.
  - destruct (fast_check t1) as [[bt ut] |] eqn:Et; invert IHt1. 2: { constructor. eapply ForT. exact Y. }
    destruct (fast_check t2) as [[bb ub] |] eqn:Eb; invert IHt2. 2: { constructor. eapply ForB. exact Y. }
    apply fast_check_bound_used in Et as [Bt Ut]. apply fast_check_bound_used in Eb as [Bb Ub].
    destruct (Map.find_spec bb variable). { constructor. apply ForVB. apply Bb. eexists. exact Y. }
    assert (D := @Map.disjoint_spec). cbn in D.
    destruct (D _ _ bt ub). 2: { constructor.
      apply Map.not_disjoint_exists in N2 as [k [Btk Ubk]]. eapply ForTB; [apply Bt | apply Ub]; eassumption. }
    destruct (D _ _ bb ut). 2: { constructor.
      apply Map.not_disjoint_exists in N2 as [k [Bbk Utk]]. eapply ForBT; [apply Bb | apply Ut]; eassumption. }
    constructor. intro C. invert C.
    + apply N in deeper_in_type as [].
    + apply N0 in deeper_in_body as [].
    + eapply Y; [apply Bt | apply Ub]; eassumption.
    + eapply Y0; [apply Bb | apply Ut]; eassumption.
    + eapply N1. apply Bb in rebound_in_body as [[] C]. exact C.
  - destruct (fast_check t1) as [[bb ub] |] eqn:Eb; invert IHt1. 2: { constructor. eapply CasB. exact Y. }
    destruct (fast_check t2) as [[bo uo] |] eqn:Eo; invert IHt2. 2: { constructor. eapply CasO. exact Y. }
    apply fast_check_bound_used in Eb as [Bb Ub]. apply fast_check_bound_used in Eo as [Bo Uo].
    assert (D := @Map.disjoint_spec). cbn in D.
    destruct (D _ _ bb (BoundIn.pattern pattern)). 2: { constructor.
      apply Map.not_disjoint_exists in N1 as [k [Bbk BP]]. eapply CasPB; [apply BoundIn.pattern_spec | apply Bb]; eassumption. }
    destruct (D _ _ bo ub). 2: { constructor.
      apply Map.not_disjoint_exists in N1 as [k [Bok Ubk]]. eapply CasOB; [apply Bo | apply Ub]; eassumption. }
    destruct (D _ _ bb uo). 2: { constructor.
      apply Map.not_disjoint_exists in N1 as [k [Bbk Uok]]. eapply CasBO; [apply Bb | apply Uo]; eassumption. }
    constructor. intro C. invert C.
    + apply N in deeper_in_body_if_match as [].
    + apply N0 in deeper_in_other_cases as [].
    + eapply Y1; [apply Bb | apply Uo]; eassumption.
    + eapply Y0; [apply Bo | apply Ub]; eassumption.
    + eapply Y; [apply Bb | apply BoundIn.pattern_spec]; eassumption.
Qed.



Import Term. Print term.
Definition unshadow_acc reserved lookup t :=
  match t with
  | _ => (t, reserved)
  | Term.Mov x =>
      let y := NewNames.new_name reserved x in
      (Term.Mov y, Map.overriding_add y tt reserved)
  | Term.Ref x =>
      let y := NewNames.new_name reserved x in
      (Term.Ref y, Map.overriding_add y tt reserved)
  | Term.App function argument =>
      let bound_in_orig_arg = BoundIn.term TODO
  end.



Inductive Unshadow {lookup} (O2O : Map.OneToOne lookup) : Term.term -> Term.term -> Prop :=
  | UErr
      : Unshadow O2O Term.Err Term.Err
  | UTyp
      : Unshadow O2O Term.Typ Term.Typ
  | UPrp
      : Unshadow O2O Term.Prp Term.Prp
  | UCtr ctor
      : Unshadow O2O (Term.Ctr ctor) (Term.Ctr ctor)
  | UMov {x y} (rename : Map.Find lookup x y)
      : Unshadow O2O (Term.Mov x) (Term.Mov y)
  | URef {x y} (rename : Map.Find lookup x y)
      : Unshadow O2O (Term.Ref x) (Term.Ref y)
  | UApp
      {function unshadowed_function} (unshadow_function : Unshadow O2O function unshadowed_function)
      {argument unshadowed_argument} (unshadow_argument : Unshadow O2O argument unshadowed_argument)
      : Unshadow O2O (Term.App function argument) (Term.App unshadowed_function unshadowed_argument)
  | UFor
      asdf.



      (E : NewNames.generate reserved names)
      {variable unshadowed_variable} (unshadow_variable : Rename.Pattern TODO
      : Unshadow O2O (Term.For variable type body) (Term.For unshadowed_variable unshadowed_type unshadowed_body0
  .
