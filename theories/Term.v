From LinearCore Require
  Constructor
  Ownership
  Pattern
  Reflect
  .
From LinearCore Require Import
  DollarSign
  Invert
  .



(* TODO: unify `Mov` and `Ref` with a boolean ownership flag *)
Inductive term : Set :=
  | Ctr (constructor : Constructor.constructor)
  | Var (name : String.string) (ownership : Ownership.ownership)
  | App (function : term) (argument : term)
  | For (variable : String.string) (type : term) (body : term)
  | Cas (pattern : Pattern.pattern) (body_if_match : term) (other_cases : term)
  .

Fixpoint eq a b :=
  match a, b with
  | Ctr a, Ctr b => Constructor.eq a b
  | Var na oa, Var nb ob => andb (String.eqb na nb) (Ownership.eq oa ob)
  | App fa aa, App fb ab => andb (eq fa fb) (eq aa ab)
  | For va ta ba, For vb tb bb => andb (String.eqb va vb) (andb (eq ta tb) (eq ba bb))
  | Cas pa ba oa, Cas pb bb ob => andb (Pattern.eq pa pb) (andb (eq ba bb) (eq oa ob))
  | _, _ => false
  end.

Lemma eq_spec a b
  : Reflect.Bool (a = b) (eq a b).
Proof.
  generalize dependent b. induction a; destruct b;
  try (constructor; intro D; discriminate D); try (constructor; reflexivity).
  - unfold eq. destruct (Constructor.eq_spec constructor constructor0); constructor. { f_equal. assumption. }
    intro E. apply N. invert E. reflexivity.
  - cbn. destruct (String.eqb_spec name name0). 2: { constructor. intro D. apply n. invert D. reflexivity. }
    subst. destruct (Ownership.eq_spec ownership ownership0); constructor. { subst. reflexivity. }
    intro D. apply N. invert D. reflexivity.
  - simpl eq. destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (String.eqb_spec variable variable0); cbn in *. 2: { constructor. intro E. apply n. invert E. reflexivity. }
    destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
  - simpl eq. destruct (Pattern.eq_spec pattern pattern0); cbn in *. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    destruct (IHa1 b1); cbn. 2: { constructor. intro E. apply N. invert E. reflexivity. }
    subst. destruct (IHa2 b2); constructor. { f_equal. assumption. } intro E. apply N. invert E. reflexivity.
Qed.



Fixpoint nodes t :=
  match t with
  | Term.App a b
  | Term.For _ a b
  | Term.Cas _ a b =>
      S $ nodes a + nodes b
  | _ => 1
  end.



From Coq Require Import
  Ascii
  String
  .

Fixpoint repeat n string :=
  match n with 0 => EmptyString | S n => append string $ repeat n string end.

Variant line_info : Set :=
  | Overflow
  | OneLiner (length : nat)
  .

Definition lmap f info :=
  match info with Overflow => Overflow | OneLiner n => OneLiner $ f n end.

Definition fits_on_line indent line_length n :=
  Nat.leb (indent + n) line_length.

Definition one_liner indent line_length info :=
  match info with
  | Overflow => false
  | OneLiner n => fits_on_line indent line_length n
  end.

Fixpoint contains char s :=
  match s with
  | EmptyString => false
  | String head tail => if Ascii.eqb char head then true else contains char tail
  end.

Definition opening_bracket : ascii := "{".

Fixpoint to_string_configurable_acc line_length indent t : line_info * (string -> string -> string) := (
  match t with
  | Ctr ctor =>
      let s := Constructor.to_string ctor in
      (OneLiner $ length s, fun _ _ => s)
  | Var name ownership =>
      if Ownership.owned ownership then
        (OneLiner $ length name, fun _ _ => name)
      else
        (OneLiner $ S $ length name, fun _ _ => "&" ++ name)
  | App (Cas pattern body_if_match other_cases) scrutinee =>
      (* TODO: detect a full match expression ending in `Err` *)
      let sp := Pattern.to_string pattern in
      let '(nb, sb) := to_string_configurable_acc line_length (S indent) body_if_match in
      let '(no, so) := to_string_configurable_acc line_length (S indent) other_cases in
      let '(ns, ss) := to_string_configurable_acc line_length (S indent) scrutinee in
      let parenthesize_scrutinee := fun _ : unit => (Overflow,
        match nb, no with
        | Overflow, Overflow => fun newline_str indent_str =>
            "if let " ++ sp ++ " = (" ++ newline_str ++
            repeat (S indent) indent_str ++ ss newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ ") {" ++ newline_str ++
            repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ "} else {" ++ newline_str ++
            repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ "}"
        | Overflow, OneLiner _ => fun newline_str indent_str =>
            "if let " ++ sp ++ " = (" ++ newline_str ++
            repeat (S indent) indent_str ++ ss newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ ") {" ++ newline_str ++
            repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ "} else { " ++ so " " "" ++ " }"
        | OneLiner _, Overflow => fun newline_str indent_str =>
            "if let " ++ sp ++ " = (" ++ newline_str ++
            repeat (S indent) indent_str ++ ss newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ ") { " ++ sb " " "" ++ " } else {" ++ newline_str ++
            repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ "}"
        | OneLiner nb, OneLiner no =>
            let projected_length := 16 + nb + no in
            if fits_on_line indent line_length projected_length then fun newline_str indent_str =>
              "if let " ++ sp ++ " = (" ++ newline_str ++
              repeat (S indent) indent_str ++ ss newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ ") { " ++ sb " " "" ++ " } else { " ++ so " " "" ++ " }"
            else fun newline_str indent_str =>
              "if let " ++ sp ++ " = (" ++ newline_str ++
              repeat (S indent) indent_str ++ ss newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ ") { " ++ sb " " "" ++ " } else {" ++ newline_str ++
              repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ "}"
        end) in
      match ns with Overflow => parenthesize_scrutinee tt | OneLiner ns =>
        let ss := ss " " "" in
        if contains opening_bracket ss then parenthesize_scrutinee tt else
        match nb, no with
        | Overflow, Overflow => (Overflow, fun newline_str indent_str =>
            "if let " ++ sp ++ " = " ++ ss ++ " {" ++ newline_str ++
            repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ "} else {" ++ newline_str ++
            repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ "}")
        | Overflow, OneLiner _ => (Overflow, fun newline_str indent_str =>
            "if let " ++ sp ++ " = " ++ ss ++ " {" ++ newline_str ++
            repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ "} else { " ++ so " " "" ++ " }")
        | OneLiner _, Overflow => (Overflow, fun newline_str indent_str =>
            "if let " ++ sp ++ " = " ++ ss ++ " { " ++ sb " " "" ++ " } else {" ++ newline_str ++
            repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
            repeat indent indent_str ++ "}")
        | OneLiner nb, OneLiner no =>
            let projected_length_psb := 22 + length sp + ns + nb in
            if fits_on_line indent line_length projected_length_psb then
              let projected_length := 3 + projected_length_psb + no in
              if fits_on_line indent line_length projected_length then (OneLiner projected_length, fun newline_str indent_str =>
                "if let " ++ sp ++ " = " ++ ss ++ " { " ++ sb " " "" ++ " } else { " ++ so " " "" ++ " }")
              else (Overflow, fun newline_str indent_str =>
                "if let " ++ sp ++ " = " ++ ss ++ " { " ++ sb " " "" ++ " } else {" ++ newline_str ++
                repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
                repeat indent indent_str ++ "}")
            else (Overflow, fun newline_str indent_str =>
              "if let " ++ sp ++ " = (" ++ newline_str ++
              repeat (S indent) indent_str ++ ss ++ newline_str ++
              repeat indent indent_str ++ ") { " ++ sb " " "" ++ " } else { " ++ so " " "" ++ " }")
        end
      end
  | App function argument =>
      let '(nf, sf) := to_string_configurable_acc line_length (S indent) function in
      let '(na, sa) := to_string_configurable_acc line_length (S indent) argument in
      match nf with
      | Overflow => (Overflow, fun newline_str indent_str => sf newline_str indent_str ++ " " ++ sa newline_str indent_str)
      | OneLiner nf =>
          match na with
          | Overflow => (Overflow, fun newline_str indent_str => sf newline_str indent_str ++ " " ++ sa newline_str indent_str)
          | OneLiner na =>
              let projected_length := S $ nf + na in
              if fits_on_line indent line_length projected_length then
                (OneLiner projected_length, fun _ _ => sf " " "" ++ " " ++ sa " " "")
              else (Overflow, fun newline_str _ => sf " " "" ++ newline_str ++ sa " " "")
          end
      end
  | For variable type body =>
      let '(nt, st) := to_string_configurable_acc line_length (S indent) type in
      let '(nb, sb) := to_string_configurable_acc line_length (S indent) body in
      match nt with
      | Overflow => (Overflow,
          match nb with
          | Overflow => fun newline_str indent_str =>
              "forall " ++ variable ++ ": (" ++ newline_str ++
              repeat (S indent) indent_str ++ st newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ ") {" ++ newline_str ++
              repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ "}"
          | OneLiner _ => fun newline_str indent_str =>
              "forall " ++ variable ++ ": (" ++ newline_str ++
              repeat (S indent) indent_str ++ st newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ ") { " ++ sb " " "" ++ " }"
          end)
      | OneLiner nt =>
          match nb with
          | Overflow => (Overflow, fun newline_str indent_str =>
              "forall " ++ variable ++ ": " ++ st " " "" ++ " {" ++ newline_str ++
              repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ "}")
          | OneLiner nb =>
              let projected_length := 12 + nt + nb in
              if fits_on_line indent line_length projected_length then (OneLiner projected_length, fun _ _ =>
                "forall " ++ variable ++ ": " ++ st " " "" ++ " {" ++ sb " " "" ++ "}")
              else (Overflow, fun newline_str indent_str =>
                "forall " ++ variable ++ ": " ++ st " " "" ++ " {" ++ newline_str ++
                repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
                repeat indent indent_str ++ "}")
          end
      end
  | Cas pattern body_if_match other_cases =>
      let sp := Pattern.to_string pattern in
      let '(nb, sb) := to_string_configurable_acc line_length (S indent) body_if_match in
      let '(no, so) := to_string_configurable_acc line_length (S indent) other_cases in
      match nb with
      | Overflow => (Overflow,
          match no with
          | Overflow => fun newline_str indent_str =>
              "case " ++ sp ++ " {" ++ newline_str ++
              repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ "} else {" ++ newline_str ++
              repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ "}"
          | OneLiner _ => fun newline_str indent_str =>
              "case " ++ sp ++ " {" ++ newline_str ++
              repeat (S indent) indent_str ++ sb newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ "} else { " ++ so " " "" ++ " }"
          end)
      | OneLiner nb =>
          match no with
          | Overflow => (Overflow, fun newline_str indent_str =>
              "case " ++ sp ++ " { " ++ sb " " "" ++ " } else {" ++ newline_str ++
              repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
              repeat indent indent_str ++ "}")
          | OneLiner no =>
              let projected_length := 20 + length sp + nb + no in
              if fits_on_line indent line_length projected_length then (OneLiner projected_length, fun _ _ =>
                "case " ++ sp ++ " { " ++ sb " " "" ++ " } else { " ++ so " " "" ++ " }")
              else (Overflow, fun newline_str indent_str =>
                "case " ++ sp ++ " { " ++ sb " " "" ++ " } else {" ++ newline_str ++
                repeat (S indent) indent_str ++ so newline_str indent_str ++ newline_str ++
                repeat indent indent_str ++ "}")
          end
      end
  end)%string.

Definition default_newline_char := Ascii.Ascii false true false true false false false false.
Arguments default_newline_char/.
Definition default_newline_str := String.String default_newline_char String.EmptyString.
Arguments default_newline_str/.
Definition default_line_length := 80.
Arguments default_line_length/.
Definition default_indent_str : string := "  ".
Arguments default_indent_str/.

Definition to_string_configurable line_length indent newline_str indent_str t :=
  let '(_, f) := to_string_configurable_acc line_length indent t in
  f newline_str indent_str.
Arguments to_string_configurable line_length indent newline_str indent_str t/.

Definition to_string_compact := to_string_configurable 0 0 " " "".
Arguments to_string_compact/ t.

Definition to_string_indent indent := to_string_configurable default_line_length indent default_newline_str "  ".
Arguments to_string_indent indent/ t.

Definition to_string := to_string_indent 0.
Arguments to_string/ t.
