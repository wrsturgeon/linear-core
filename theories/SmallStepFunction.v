From Equations Require Import
  Equations
  .
From LinearCore Require
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
Definition to_string (opt : option (Context.context * Term.term)) : string :=
  match opt with None => "<abort>" | Some (context, term) =>
    let '(line_length, format_term) := Term.to_string_configurable_acc Term.default_line_length 0 term in
    let term_formatted := format_term Term.default_newline_str Term.default_indent_str in
    let dividing_line_length :=
      match line_length with
      | Term.Overflow => Term.default_line_length
      | Term.OneLiner n => n
      end in
    let dividing_line := Term.repeat dividing_line_length "=" in
    (*let dividing_line := Term.repeat Term.default_line_length "=" in*)
    Map.fold (fun k v acc => (k ++ " |-> " ++ Term.to_string v ++ Term.default_newline_str ++ acc)%string)
    (String.append dividing_line $ String.append Term.default_newline_str term_formatted) context
  end.



(* TODO: Much later, instead of continually checking all bound and used terms in `unshadowed`,
 * consider keeping a running tally of all bound and used terms, then
 * incrementally updating it with each step, to cache most of the work. *)

Equations step (context : Context.context) (term : Term.term)
  : option (Context.context * Term.term) by wf (Nat.add (Term.nodes term) $
    List.fold_right (fun kv => Nat.add $ Term.nodes $ snd kv) 0 $ MapCore.bindings context) lt :=
  step context (Term.Var name Ownership.Owned) :=
    match Map.find context name with None => None | Some updated_term =>
      Some (Map.remove name context, updated_term)
    end;
  step context (Term.Var self Ownership.Referenced) with Map.found_dec context self => {
  | Map.NotFound => None
  | @Map.Found looked_up _ =>
      let context_without_self := Map.remove self context in
      match step context_without_self looked_up with None => None | Some (updated_context_without_self, stepped) =>
        match Map.find updated_context_without_self self with Some _ => None | None =>
          Some (Map.overriding_add self stepped updated_context_without_self, Term.Var self Ownership.Referenced)
        end
      end };
  step context (Term.App function argument) :=
    match step context function with
    | Some (updated_context, updated_function) => Some (updated_context, Term.App updated_function argument)
    | None =>
        match function with
        | Term.Cas pattern body_if_match other_cases => (* TODO: simplify `Unshadow.unshadowed` below *)
            if andb (Match.compatible context pattern) (Unshadow.unshadowed $ Term.App function argument) then
              match pattern with
              | Pattern.Nam name => Some (Map.overriding_add name argument context, body_if_match)
              | Pattern.Pat move_or_reference =>
                  match Shape.shape_or_ref context argument with
                  | Some _ =>
                      match Match.move_or_reference context move_or_reference argument with
                      | None => Some (context, Term.App other_cases argument)
                      | Some context_with_matches => Some (context_with_matches, body_if_match)
                      end
                  | None =>
                      match step context argument with None => None | Some (updated_context, reduced_scrutinee) =>
                        Some (updated_context, Term.App (Term.Cas pattern body_if_match other_cases) reduced_scrutinee)
                      end
                  end
              end
            else (* TODO: simplify `Unshadow.unshadowed` below *)
              option_map (pair context) $ Unshadow.unshadow_reserve (Map.domain context) $ Term.App function argument
        | _ => None
        end
    end;
  step _ _ := None.
Next Obligation.
  clear step. assert (BS := Map.bindings_remove_split Y). apply MapCore.bindings_spec1 in Y.
  destruct BS as [bl [br [-> ->]]]; clear context Y. repeat rewrite List.fold_right_app. cbn.
  induction bl as [| [k v] tail IH]; cbn in *. { apply PeanoNat.Nat.lt_succ_diag_r. }
  rewrite PeanoNat.Nat.add_assoc. rewrite (PeanoNat.Nat.add_comm $ Term.nodes looked_up). rewrite plus_n_Sm.
  rewrite <- PeanoNat.Nat.add_assoc. apply PeanoNat.Nat.add_lt_mono_l. exact IH. Qed.
Next Obligation.
  rewrite <- PeanoNat.Nat.add_assoc. rewrite plus_n_Sm. apply PeanoNat.Nat.add_lt_mono_l.
  rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. Qed.
Next Obligation.
  rewrite (PeanoNat.Nat.add_comm $ Term.nodes function).
  rewrite <- PeanoNat.Nat.add_assoc. rewrite plus_n_Sm. apply PeanoNat.Nat.add_lt_mono_l.
  rewrite <- PeanoNat.Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply PeanoNat.Nat.lt_0_succ. Qed.
Fail Next Obligation.



Theorem spec context term
  : Reflect.Option (fun pair => SmallStep.Step context term (fst pair) (snd pair)) (step context term).
Proof.
  funelim (step context term); try solve [constructor; intros [] S; invert S].
  - destruct (Map.find_spec context name); constructor; cbn in *.
    + constructor. { exact Y. } apply Map.remove_remove. eexists. exact Y.
    + intros [updated_context updated_term] S; cbn in *. invert S. apply N in lookup as [].
  - clear Heqcall. destruct H as [[updated_context updated_function] |]. { constructor. cbn in *. constructor. exact Y. }
    destruct function; try solve [constructor; intros [c t] S; invert S; cbn in *; apply (N (_, _)) in reduce_function as []].
    destruct andb eqn:E. 2: {
      apply Bool.andb_false_iff in E. destruct Unshadow.unshadow_reserve eqn:Eu; constructor.
      * cbn. eapply SmallStep.ApR. 3: { exact Eu. } 2: { apply Map.domain_domain. } 2: { apply Map.eq_refl. }
        destruct E as [E | E]; [left | right]; intro C.
        -- apply Match.compatible_iff in C. rewrite E in C. discriminate C.
        -- apply Unshadow.unshadowed_iff in C. rewrite E in C. discriminate C.
      * intros [c' t'] C. simpl fst in *. simpl snd in *. invert C; try solve [destruct E as [E | E]; [
          apply Match.compatible_iff in compatible_names; rewrite E in compatible_names; discriminate compatible_names |
          apply Unshadow.unshadowed_iff in unshadowed; rewrite E in unshadowed; discriminate unshadowed]]. {
          apply (N (_, _)) in reduce_function as []. }
        assert (Ed : Map.Eq (Map.domain context) context_domain). {
          eapply Map.domain_det. { apply Map.domain_domain. } 2: { exact D. } apply Map.eq_refl. }
        destruct (Unshadow.det_reserve Ed (@eq_refl _ $ Term.App (Term.Cas pattern function1 function2) argument)).
        rewrite Eu in rename. discriminate rename. }
    apply Bool.andb_true_iff in E as [MC US]. apply Match.compatible_iff in MC. apply Unshadow.unshadowed_iff in US.
    destruct pattern. { constructor. cbn. apply SmallStep.ApM; try assumption. invert MC.
      constructor. { assumption. } apply Map.add_overriding. intros v F. contradiction N0. eexists. exact F. }
    destruct (Shape.shape_or_ref_spec context argument).
    + destruct (Match.move_or_reference_spec context move_or_reference argument); constructor; cbn.
      * apply SmallStep.ApM. { exact MC. } { exact US. } constructor. exact Y0.
      * eapply SmallStep.ApN. { exact MC. } { exact US. } 2: { exact Y. } 2: { apply Map.eq_refl. }
        intros ? P. invert P. apply N0 in move_or_reference_matched as [].
    + destruct H0 as [[updated_context reduced_scrutinee] |]; constructor; try solve [repeat constructor].
      * cbn in *. apply SmallStep.ApS. { exact MC. } { exact US. } 2: { exact Y. } intros ? P. invert P.
        apply Match.move_or_reference_shape_or_ref in move_or_reference_matched as SR. apply N0 in SR as [].
      * intros [c t] C. cbn in *. invert C.
        -- apply (N (_, _)) in reduce_function as [].
        -- invert matched. apply Match.move_or_reference_shape_or_ref in move_or_reference_matched.
           apply N0 in move_or_reference_matched as [].
        -- apply (N1 (_, _)) in reduce_scrutinee as [].
        -- apply N0 in scrutinee_reduced as [].
        -- destruct not_yet_safe_to_match as [NS | NS]; apply NS. { exact MC. } exact US.
  - destruct H as [[updated_context_without_self stepped] |].
    + destruct (Map.find_spec updated_context_without_self self); constructor; cbn in *.
      * intros [c t] S. cbn in *. invert S. apply not_overwriting_self.
        eassert (Er : Map.Eq _ _); [| eassert (El : _ = _); [| assert (D := SmallStep.det Y0 Er El step_in_context)]].
        -- eapply Map.remove_det. { apply Map.remove_remove. eexists. exact lookup. } { reflexivity. } { apply Map.eq_refl. } assumption.
        -- eapply Map.find_det; eassumption.
        -- eexists. apply D. exact Y1.
      * econstructor. { exact Y. } { apply Map.remove_remove. eexists. exact Y. } { exact Y0. } { intros [y F]. apply N in F as []. }
        apply Map.add_overriding. intros stepped' F. apply N in F as [].
    + constructor. intros [c t] S. cbn in *. invert S. eapply (N (_, _)).
      eapply SmallStep.eq. { exact step_in_context. } 2: { eapply Map.find_det; eassumption. } 2: { apply Map.eq_refl. } 2: { reflexivity. }
      eapply Map.remove_det. { exact remove_self_from_context. } { reflexivity. } { apply Map.eq_refl. }
      apply Map.remove_remove. eexists. exact Y.
  - constructor. intros [c t] S. cbn in *. invert S. apply N in lookup as [].
Qed.
