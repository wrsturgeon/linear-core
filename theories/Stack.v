(* Just a non-empty list. *)

Variant stack (T : Type) : Type :=
  | Stack (head : T) (tail : list T)
  .
Arguments Stack {T} head tail.



Definition to_list {T} (stack : stack T) :=
  match stack with Stack head tail =>
    cons head tail
  end.

Definition from_list {T} (list : list T) :=
  match list with
  | nil => None
  | cons head tail => Some (Stack head tail)
  end.



Definition push {T} (x : T) (stack : stack T) :=
  cons x (to_list stack).

Definition pop {T} (stack : stack T) :=
  match stack with Stack head tail =>
    from_list tail
  end.
