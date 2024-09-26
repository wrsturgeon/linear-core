From Coq Require
  Morphisms
  RelationClasses
  .
From Coq Require Import
  Ascii
  String
  .
From LinearCore Require
  Reflect
  .
From LinearCore Require Import
  DollarSign
  Invert.



Definition AsciiBetween (min max c : Ascii.ascii) : Prop :=
  (c ?= min)%char <> Lt /\ (c ?= max)%char <> Gt.
Arguments AsciiBetween min max c/.

Definition ascii_between (min max c : Ascii.ascii) :=
  match (c ?= min)%char with Lt => false | _ =>
    match (c ?= max)%char with Gt => false | _ =>
      true
    end
  end.
Arguments ascii_between min max c/.

Lemma ascii_between_spec min max c
  : Reflect.Bool (AsciiBetween min max c) (ascii_between min max c).
Proof.
  cbn. destruct (c ?= min)%char; [| constructor; intros [N _]; apply N; reflexivity |];
  destruct (c ?= max)%char; constructor; try (intros [_ N]; apply N; reflexivity);
  split; intro D; discriminate D.
Qed.



Definition Digit := AsciiBetween "0" "9".
Arguments Digit/ c.

Definition digit := ascii_between "0" "9".
Arguments digit/ c.

Lemma digit_spec c : Reflect.Bool (Digit c) (digit c). Proof. apply ascii_between_spec. Qed.



Definition Letter := AsciiBetween "A" "z".
Arguments Letter/ c.

Definition letter := ascii_between "A" "z".
Arguments letter/ c.

Lemma letter_spec c : Reflect.Bool (Letter c) (letter c). Proof. apply ascii_between_spec. Qed.



Definition ValidCharacter (c : Ascii.ascii) : Prop :=
  Digit c \/ Letter c \/ c = "-"%char (* \/ c = "'"%char \/ c = "_"%char *).
Arguments ValidCharacter c/.

Definition valid_character c := orb (digit c) $ orb (letter c) (c =? "-")%char.
Arguments valid_character c/.

Lemma valid_character_spec c
  : Reflect.Bool (ValidCharacter c) (valid_character c).
Proof.
  apply Reflect.or. { apply digit_spec. } apply Reflect.or. { apply letter_spec. }
  destruct (Ascii.eqb_spec c "-"); constructor; assumption.
Qed.



Inductive Primes : string -> Prop :=
  | PNil
      : Primes EmptyString
  | PCons {tail} (etc : Primes tail)
      : Primes $ String "'" tail
  .
Arguments Primes s.

Fixpoint primes s :=
  match s with EmptyString => true | String head tail =>
    andb (head =? "'")%char $ primes tail
  end.

Lemma primes_spec s
  : Reflect.Bool (Primes s) (primes s).
Proof.
  induction s; cbn. { constructor. constructor. }
  destruct (Ascii.eqb_spec a "'"). 2: { constructor. intro C. invert C. apply n. reflexivity. }
  subst. destruct IHs; constructor. { constructor. exact Y. } intro C. invert C. apply N in etc as [].
Qed.



Inductive ValidTail : string -> Prop :=
  | VPrimes {primes} (all_rest_primes : Primes primes)
      : ValidTail primes
  | VCons {head} (valid_first : ValidCharacter head) {tail} (etc : ValidTail tail)
      : ValidTail $ String head tail
  .
Arguments ValidTail s.

Fixpoint valid_tail s :=
  if primes s then true else
    match s with EmptyString => true | String head tail =>
      andb (valid_character head) (valid_tail tail)
    end.

Lemma valid_tail_string head tail
  : valid_tail (String head tail) = orb (andb (head =? "'")%char $ primes tail) $ andb (valid_character head) (valid_tail tail).
Proof. reflexivity. Qed.

Lemma valid_tail_spec s
  : Reflect.Bool (ValidTail s) (valid_tail s).
Proof.
  induction s. { constructor. constructor. constructor. } rewrite valid_tail_string. destruct (Ascii.eqb_spec a "'").
  - subst. cbn. destruct (primes_spec s); constructor. { constructor. constructor. exact Y. }
    intro C. invert C. { invert all_rest_primes. apply N in etc as []. } cbn in valid_first.
    destruct valid_first as [[C _] | [[C _] | D]]; try (contradiction C; reflexivity); discriminate D.
  - rewrite Bool.andb_false_l. rewrite Bool.orb_false_l. destruct (valid_character_spec a). 2: {
      constructor. intro C. invert C. { invert all_rest_primes. apply n. reflexivity. } apply N in valid_first as []. }
    cbn. destruct IHs; constructor. { apply VCons. { exact Y. } exact Y0. }
    intro C. invert C. invert all_rest_primes. { apply n. reflexivity. } apply N in etc as [].
Qed.



Definition Valid s := exists head tail, Letter head /\ ValidTail tail /\ s = String head tail.
Arguments Valid s/.

Definition valid s :=
  match s with EmptyString => false | String head tail =>
    andb (letter head) (valid_tail tail)
  end.
Arguments valid s/.

Lemma valid_spec s
  : Reflect.Bool (Valid s) (valid s).
Proof.
  unfold valid. destruct s. { constructor. intros [head [tail [L [V E]]]]. discriminate E. }
  destruct (letter_spec a). 2: { constructor. intros [head [tail [L [V E]]]]. invert E. apply N in L as []. }
  destruct (valid_tail_spec s); constructor. { do 2 eexists. split. { exact Y. } split. { exact Y0. } reflexivity. }
  intros [head [tail [L [V E]]]]. invert E. apply N in V as [].
Qed.
