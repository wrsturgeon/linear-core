From LinearCore Require
  Map
  Pattern
  Term
  .
From LinearCore Require Import
  Invert
  .



Inductive Raw : forall (pattern : Pattern.raw) (term : Term.term) (matches : Map.to Term.term), Prop :=
  | Ctr matches (E : Map.Empty matches) ctor
      : Raw (Pattern.Ctr ctor) (Term.Ctr ctor) matches
  | App
      function_pattern function function_matches (function_matched : Raw function_pattern function function_matches)
      argument_name (N : forall (I : Map.In function_matches argument_name), False)
      (* can't match the same name twice in the same pattern ^^^ *)
      argument matches (A : Map.Add argument_name argument function_matches matches)
      : Raw (Pattern.App function_pattern argument_name) (Term.App function argument) matches
  .

Fixpoint raw pattern term :=
  match pattern, term with
  | Pattern.Ctr constructor_pattern, Term.Ctr constructor =>
      if Constructor.eq constructor_pattern constructor then Some Map.empty else None
  | Pattern.App function_pattern argument_name, Term.App function argument =>
      match raw function_pattern function with None => None | Some function_matches =>
        Map.checked_add Term.eq argument_name argument function_matches
      end
  | _, _ => None
  end.
