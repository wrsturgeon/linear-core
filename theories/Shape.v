From LinearCore Require
  Term
  .



Variant shape : Set :=
  | Resource
  | Function
  .



Inductive Shape : shape -> Term.term -> Prop :=
  | Ctr ctor
      : Shape Resource (Term.Ctr ctor)
  | App curried (curried_resource : Shape Resource curried) argument
      : Shape Resource (Term.App curried argument)
  | Cas pattern body_if_match other_cases
      : Shape Function (Term.Cas pattern body_if_match other_cases)
  .
