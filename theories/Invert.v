Tactic Notation "invert" hyp(H) := inversion H; clear H; subst.

Tactic Notation "invert" hyp(H) "as" simple_intropattern(P) := inversion H as P; clear H; subst.
