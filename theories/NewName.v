From LinearCore Require
  Map
  Name
  .



Import Ascii.
Definition underscore := "_"%char.

Definition underscored name :=
  match name with
  | Name.Name head tail => Name.Name underscore (String.String head tail)
  end.



Axiom new_name : Map.set -> Name.name -> Name.name.
Arguments new_name reserved orig_name.
Extract Constant new_name =>
  "let rec new_name' reserved name = if Map.in_ name reserved then unbound' (underscored name) reserved else name in new_name'".

Axiom not_in_new_name : forall reserved orig_name (I : Map.In reserved (new_name reserved orig_name)), False.
Arguments not_in_new_name {reserved orig_name} I.

Axiom new_name_eq : forall r1 r2 (E : Map.Eq r1 r2) orig_name, new_name r1 orig_name = new_name r2 orig_name.
Arguments new_name_eq {r1 r2} E orig_name.
