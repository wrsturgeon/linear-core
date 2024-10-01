From LinearCore Require
  Fuel
  Halt
  SmallStep
  Term
  Unshadow
  VerbosePrint
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



From Coq Require Import String.
Definition to_string (h : Halt.halt (Context.context * Term.term)) : string :=
  match h with
  | Halt.Return (ctx, t) => Term.to_string t ++ " with " ++ Context.to_string ctx
  | Halt.Exit => "<abort>"
  | Halt.OutOfFuel => "<out of time>"
  end.

(* TODO: Much later, instead of continually checking all bound and used terms in `unshadowed`,
 * consider keeping a running tally of all bound and used terms, then
 * incrementally updating it with each step, to cache most of the work. *)

Fixpoint step (fuel : Fuel.fuel) (context : Context.context) (term : Term.term) : Halt.halt (Context.context * Term.term) :=
  VerbosePrint.format to_string $
  match fuel with Fuel.Stop => Halt.OutOfFuel | Fuel.Continue fuel =>
    match term with
    | Term.Mov name =>
        match Map.find context name with
        | None => Halt.Exit
        | Some updated_term => Halt.Return (Map.remove name context, updated_term)
        end
    | Term.Ref self =>
        match Map.find context self with None => Halt.Exit | Some looked_up =>
          let context_without_self := Map.remove self context in
          match step fuel context_without_self looked_up with
          | Halt.Return (updated_context_without_self, stepped) =>
            match Map.find updated_context_without_self self with Some _ => Halt.Exit | None =>
              Halt.Return (Map.overriding_add self stepped updated_context_without_self, Term.Ref self)
            end
          | other => other
          end
        end
    | Term.App (Term.Cas pattern body_if_match other_cases) scrutinee =>
        if andb (Match.compatible context pattern) (Unshadow.unshadowed term) then
          Halt.Exit (* TODO *)
        else
          match Unshadow.unshadow_reserve (Map.domain context) term with
          | None => Halt.Exit
          | Some renamed => Halt.Return (context, renamed)
          end
    | _ => Halt.Exit
    end
  end.



Theorem spec fuel context term
  : Reflect.Halt (fun pair => SmallStep.Step context term (fst pair) (snd pair)) (step fuel context term).
Proof.
  generalize dependent term. generalize dependent context. induction fuel. { constructor. }
  destruct term; try solve [constructor; intros [updated_context updated_term] S; cbn in *; invert S].
  - cbn in *. destruct (Map.find_spec context name); constructor; cbn in *.
    + constructor. { exact Y. } apply Map.remove_remove. eexists. exact Y.
    + intros [updated_context updated_term] S; cbn in *. invert S. apply N in lookup as [].
  - cbn in *. destruct (Map.find_spec context name). 2: {
      constructor. intros [m t] C; cbn in *. invert C. apply N in lookup as []. }
    destruct (IHfuel (Map.remove name context) x). 3: { constructor. } 2: {
      constructor. intros [m t] C; cbn in *. invert C. eapply (N (_, _)). eapply SmallStep.eq.
      * exact step_in_context.
      * intros x' y'. destruct remove_self_from_context as [I R]. cbn in R. rewrite R.
        destruct (Map.remove_remove I) as [_ R']. cbn in R'. rewrite R'. reflexivity.
      * eapply Map.find_det; eassumption.
      * apply Map.eq_refl.
      * reflexivity. }
    destruct x0 as [updated_context_without_self stepped]; cbn in *.
    destruct (Map.find_spec updated_context_without_self name); constructor. {
      intros [m t] C; cbn in *. invert C.
      eassert (Er : _); [| eassert (Ex : _); [| destruct (SmallStep.det Y0 Er Ex step_in_context) as [D1 D2]]].
      * intros x' y'. destruct remove_self_from_context as [I R]. cbn in R. rewrite R.
        destruct (Map.remove_remove I) as [_ R']. cbn in R'. rewrite R'. reflexivity.
      * eapply Map.find_det; eassumption.
      * subst. apply not_overwriting_self. eexists. apply D1. eassumption. }
    cbn. econstructor. { exact Y. } { apply Map.remove_remove. eexists. exact Y. } { exact Y0. }
    + intros [y F]. apply N in F as [].
    + apply Map.add_overriding. intros v F. apply N in F as [].
  - unfold step. unfold VerbosePrint.format. unfold VerbosePrint.print.
    destruct term1 as [| | | | | pattern body_if_match other_cases];
    try solve [constructor; intros [m t] C; invert C]. destruct andb eqn:E. 2: {
      apply Bool.andb_false_iff in E. destruct Unshadow.unshadow_reserve eqn:Eu; constructor.
      * cbn. eapply SmallStep.ApR. 3: { exact Eu. } 2: { apply Map.domain_domain. } 2: { apply Map.eq_refl. }
        destruct E as [E | E]; [left | right]; intro C.
        -- apply Match.compatible_iff in C. rewrite E in C. discriminate C.
        -- apply Unshadow.unshadowed_iff in C. rewrite E in C. discriminate C.
      * intros [c' t'] C. simpl fst in *. simpl snd in *. invert C; try solve [destruct E as [E | E]; [
          apply Match.compatible_iff in compatible_names; rewrite E in compatible_names; discriminate compatible_names |
          apply Unshadow.unshadowed_iff in unshadowed; rewrite E in unshadowed; discriminate unshadowed]].
        assert (Ed : Map.Eq (Map.domain context) context_domain). {
          eapply Map.domain_det. { apply Map.domain_domain. } 2: { exact D. } apply Map.eq_refl. }
        destruct (Unshadow.det_reserve Ed (@eq_refl _ $ Term.App (Term.Cas pattern body_if_match other_cases) term2)).
        rewrite Eu in rename. discriminate rename. }
Abort.
