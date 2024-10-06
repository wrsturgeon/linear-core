From Equations Require Import
  Equations
  .
From LinearCore Require
  BoundIn
  Context
  Map
  Term
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



Inductive Term : Term.term -> String.string -> Prop :=
  | Var name ownership
      : Term (Term.Var name ownership) name
  | ApF function name (used_in_function : Term function name) argument
      : Term (Term.App function argument) name
  | ApA argument name (used_in_argument : Term argument name) function
      : Term (Term.App function argument) name
  | FoT type name (used_in_type : Term type name) variable body
      : Term (Term.For variable type body) name
  | FoB name variable (not_shadowed : name <> variable) body (used_in_body : Term body name) type
      : Term (Term.For variable type body) name
  | CaB pattern name (not_shadowed : forall (B : BoundIn.Pattern pattern name), False)
      body_if_match (used_in_body : Term body_if_match name) other_cases
      : Term (Term.Cas pattern body_if_match other_cases) name
  | CaO other_cases name (used_in_another_case : Term other_cases name) pattern body_if_match
      : Term (Term.Cas pattern body_if_match other_cases) name
  .
Arguments Term term name.

Fixpoint term t : Map.set :=
  match t with
  | Term.Var name _ =>
      Map.singleton name tt
  | Term.App function argument =>
      Map.set_union (term function) (term argument)
  | Term.For variable type body =>
      Map.set_union (term type) (Map.remove variable (term body))
  | Term.Cas pattern body_if_match other_cases =>
      Map.set_union (term other_cases) (Map.minus (term body_if_match) (BoundIn.pattern pattern))
  | _ => Map.empty
  end.

Lemma term_spec t
  : Map.Reflect (Term t) (term t).
Proof.
  induction t; cbn in *; intros.
  - split. { intros [v F]. invert F. } intro T. invert T.
  - split. { intros [v F]. apply Map.find_singleton in F as [-> ->]. constructor. }
    intro T. invert T. eexists. apply Map.find_singleton. split; reflexivity.
  - split.
    + intros [v F]. eapply Map.union_overriding in F as [F | F];
      [apply ApF; apply IHt1 | apply ApA; apply IHt2 |]; try (eexists; exact F).
      intros ? [] ? []. reflexivity.
    + intro T. invert T; [apply IHt1 in used_in_function as [v IH] | apply IHt2 in used_in_argument as [v IH]];
      eexists; (apply Map.union_overriding; [intros ? [] ? []; reflexivity |]); [left | right]; exact IH.
  - split.
    + intros [v F]. apply Map.union_overriding in F as [F | F]; [| | intros ? [] ? []; reflexivity]. {
        apply FoT. apply IHt1. eexists. exact F. }
      eapply Map.find_remove_if_present in F as [N F]. 2: { apply Map.remove_if_present_remove. }
      apply FoB. { exact N. } apply IHt2. eexists. exact F.
    + intro T. invert T; [apply IHt1 in used_in_type as [v IH] | apply IHt2 in used_in_body as [v IH]];
      eexists; (apply Map.union_overriding; [intros ? [] ? []; reflexivity |]); [left | right]. { exact IH. }
      eapply Map.find_remove_if_present. { apply Map.remove_if_present_remove. } split; eassumption.
  - split.
    + intros [v F]. apply Map.union_overriding in F as [F | F]; [| | intros ? [] ? []; reflexivity]. {
        apply CaO. apply IHt2. eexists. exact F. }
      apply Map.minus_minus in F as [F N]. apply CaB. 2: { eapply IHt1. eexists. exact F. }
      intro B. apply N. apply BoundIn.pattern_iff. exact B.
    + intro T. invert T; [apply IHt1 in used_in_body as [v IH] | apply IHt2 in used_in_another_case as [v IH]];
      eexists; (apply Map.union_overriding; [intros ? [] ? []; reflexivity |]); [right | left]. 2: { exact IH. }
      apply Map.minus_minus. split. { exact IH. } intro B. apply not_shadowed. apply BoundIn.pattern_iff. exact B.
Qed.



Inductive Indirect : Context.context -> Term.term -> String.string -> Prop :=
  | ITransitive {context id term leftover} (F : Map.Pop context id term leftover)
      {name} (transitive : Indirect leftover term name) ownership
      : Indirect context (Term.Var id ownership) name
  | IVar context name ownership
      : Indirect context (Term.Var name ownership) name
  | IApF {context function name} (used_in_function : Indirect context function name) argument
      : Indirect context (Term.App function argument) name
  | IApA {context argument name} (used_in_argument : Indirect context argument name) function
      : Indirect context (Term.App function argument) name
  | IFoT {context type name} (used_in_type : Indirect context type name) variable body
      : Indirect context (Term.For variable type body) name
  | IFoB {name variable} (not_shadowed : name <> variable) {context body} (used_in_body : Indirect context body name) type
      : Indirect context (Term.For variable type body) name
  | ICaB {pattern name} (not_shadowed : forall (B : BoundIn.Pattern pattern name), False)
      {context body_if_match} (used_in_body : Indirect context body_if_match name) other_cases
      : Indirect context (Term.Cas pattern body_if_match other_cases) name
  | ICaO {context other_cases name} (used_in_another_case : Indirect context other_cases name) pattern body_if_match
      : Indirect context (Term.Cas pattern body_if_match other_cases) name
  .
Arguments Indirect context term name.

Lemma indirect_superset {lil t x} (U : Indirect lil t x) {big} (S : Map.Subset lil big)
  : Indirect big t x.
Proof.
  generalize dependent big. induction U; intros.
  - destruct F as [F R]. eapply ITransitive; [| apply IHU].
    + split. { apply S. exact F. } apply Map.remove_if_present_remove.
    + intros k v F'. apply R in F' as [N' F']. apply Map.remove_if_present_remove.
      split. { exact N'. } apply S. exact F'.
  - apply IVar.
  - apply IApF. apply IHU. exact S.
  - apply IApA. apply IHU. exact S.
  - apply IFoT. apply IHU. exact S.
  - apply IFoB. { exact not_shadowed. } apply IHU. exact S.
  - apply ICaB. { exact not_shadowed. } apply IHU. exact S.
  - apply ICaO. apply IHU. exact S.
Qed.

(* NOTE: Depending on the chainedness of the context, this could be powerfully inefficient,
 * since we aren't marking visited notes to skip later. However, this is easier to prove. *)
Equations indirect (context : Context.context) (t : Term.term) : Map.set by wf (Nat.add (Term.nodes t) $
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 $ MapCore.bindings context) lt :=
  indirect context (Term.Var name _) with Map.found_dec context name => {
    | Map.NotFound => Map.singleton name tt
    | @Map.Found looked_up _ => Map.set_add name $ indirect (Map.remove name context) looked_up };
  indirect _ (Term.App function argument) :=
      Map.set_union (indirect context function) (indirect context argument);
  indirect _ (Term.For variable type body) :=
      Map.set_union (indirect context type) (Map.remove variable (indirect context body));
  indirect _ (Term.Cas pattern body_if_match other_cases) :=
      Map.set_union (indirect context other_cases) (Map.minus (indirect context body_if_match) (BoundIn.pattern pattern));
  indirect _ _ := Map.empty.
Next Obligation.
  clear indirect. assert (F := Y). apply MapCore.bindings_spec1 in F. destruct (Map.bindings_remove_split Y) as [bl [br [Ec Er]]].
  clear Y. repeat rewrite Ec in *; repeat rewrite Er in *; clear context ownership Ec Er. repeat rewrite List.fold_right_app. cbn.
  induction bl as [| [k v] tail IH]; cbn in *. { apply PeanoNat.Nat.lt_succ_diag_r. }
  rewrite PeanoNat.Nat.add_assoc. rewrite (PeanoNat.Nat.add_comm $ Term.nodes looked_up). rewrite plus_n_Sm.
  rewrite <- PeanoNat.Nat.add_assoc. apply PeanoNat.Nat.add_lt_mono_l. apply IH.
  apply SetoidList.InA_app_iff. right. left. split; reflexivity. Qed.
Next Obligation.
  rewrite <- PeanoNat.Nat.add_assoc. rewrite plus_n_Sm. apply PeanoNat.Nat.add_lt_mono_l.
  rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. Qed.
Next Obligation.
  rewrite (PeanoNat.Nat.add_comm $ Term.nodes function).
  rewrite <- PeanoNat.Nat.add_assoc. rewrite plus_n_Sm. apply PeanoNat.Nat.add_lt_mono_l.
  rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. Qed.
Next Obligation.
  rewrite <- PeanoNat.Nat.add_assoc. repeat rewrite (plus_n_Sm $ Term.nodes type). apply PeanoNat.Nat.add_lt_mono_l.
  repeat rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. Qed.
Next Obligation.
  rewrite (PeanoNat.Nat.add_comm $ Term.nodes type).
  rewrite <- PeanoNat.Nat.add_assoc. repeat rewrite (plus_n_Sm $ Term.nodes body). apply PeanoNat.Nat.add_lt_mono_l.
  repeat rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. Qed.
Next Obligation.
  repeat rewrite <- PeanoNat.Nat.add_assoc. rewrite (PeanoNat.Nat.add_assoc $ Term.nodes body_if_match).
  rewrite (PeanoNat.Nat.add_comm $ Term.nodes body_if_match). repeat rewrite PeanoNat.Nat.add_assoc.
  rewrite (PeanoNat.Nat.add_comm $ Pattern.nodes _). repeat rewrite <- PeanoNat.Nat.add_assoc.
  rewrite plus_n_Sm. apply PeanoNat.Nat.add_lt_mono_l. repeat rewrite PeanoNat.Nat.add_assoc.
  rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. Qed.
Next Obligation.
  rewrite (PeanoNat.Nat.add_comm $ Pattern.nodes _). repeat rewrite <- PeanoNat.Nat.add_assoc.
  rewrite plus_n_Sm. apply PeanoNat.Nat.add_lt_mono_l. repeat rewrite PeanoNat.Nat.add_assoc.
  rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. Qed.
Fail Next Obligation.

Lemma indirect_spec context t
  : Map.Reflect (Indirect context t) (indirect context t).
Proof.
  funelim (indirect context t).
  - split; intro I. { apply Map.empty_empty in I as []. } invert I.
  - split; intro I.
    + apply Map.in_overriding_union in I as [I | I]; [apply H in I | apply H0 in I]; [apply IApF | apply IApA]; exact I.
    + apply Map.in_overriding_union. invert I; [left | right]; [apply H | apply H0]; assumption.
  - split; intro I.
    + apply Map.in_overriding_union in I as [I | I]. { apply H in I. apply IFoT. exact I. }
      eapply Map.in_remove_if_present in I as [N I]. 2: { apply Map.remove_if_present_remove. }
      apply IFoB. { exact N. } apply H0. exact I.
    + apply Map.in_overriding_union. invert I; [left | right]. { apply H. exact used_in_type. }
      eapply Map.in_remove_if_present. { apply Map.remove_if_present_remove. }
      split. { exact not_shadowed. } apply H0. exact used_in_body.
  - split; intro I.
    + apply Map.in_overriding_union in I as [I | I]. { apply H in I. apply ICaO. exact I. }
      destruct I as [[] F]. apply Map.minus_minus in F as [F N]. apply ICaB. 2: { apply H0. eexists. exact F. }
      intro B. apply N. apply BoundIn.pattern_iff. exact B.
    + apply Map.in_overriding_union. invert I; [right | left]. 2: { apply H. exact used_in_another_case. }
      exists tt. apply Map.minus_minus. apply H0 in used_in_body as [[] F]. split. { exact F. }
      intro B. apply not_shadowed. apply BoundIn.pattern_iff. exact B.
  - split; intro I.
    + apply Map.in_overriding_add in I as [-> | I]. { constructor. } econstructor. 2: { apply H. exact I. }
      split. { exact Y. } apply Map.remove_if_present_remove.
    + apply Map.in_overriding_add. invert I; [right | left]. 2: { reflexivity. }
      apply H. destruct F as [F R]. destruct (Map.find_det Y F). eapply indirect_superset. { exact transitive. }
      intros k v F'. apply R in F' as [N' F']. apply Map.remove_if_present_remove. split. { exact N'. } exact F'.
  - split; intro I. { apply Map.in_singleton in I as ->. constructor. } apply Map.in_singleton.
    invert I. 2: { reflexivity. } destruct F as [R F]. apply N in R as [].
Qed.
