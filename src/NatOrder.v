Require Import UniMath.MoreFoundations.All.

Proposition natgthorleh_left
            {m n : ℕ}
            (p : m > n)
  : natgthorleh m n = inl p.
Proof.
  destruct (natgthorleh m n) as [ q | q ].
  - apply maponpaths.
    apply propproperty.
  - apply fromempty.
    use (natlehtonegnatgth _ _ q).
    exact p.
Qed.

Proposition natgthorleh_right
            {m n : ℕ}
            (p : m ≤ n)
  : natgthorleh m n = inr p.
Proof.
  destruct (natgthorleh m n) as [ q | q ].
  + apply fromempty.
    use (natlehtonegnatgth _ _ p).
    exact q.
  + apply maponpaths.
    apply propproperty.
Qed.

Proposition natlehchoice_left
            {m n : ℕ}
            (p : m ≤ n)
            (q : m < n)
  : natlehchoice m n p = inl q.
Proof.
  destruct (natlehchoice m n p) as [ r | r ].
  - apply maponpaths.
    apply propproperty.
  - induction r.
    apply fromempty.
    use (isirreflnatlth m).
    exact q.
Qed.

Proposition natlehchoice_right
            {m n : ℕ}
            (p : m ≤ n)
            (q : m = n)
  : natlehchoice m n p = inr q.
Proof.
  destruct (natlehchoice m n p) as [ r | r ].
  - induction q.
    apply fromempty.
    use (isirreflnatlth m).
    exact r.
  - apply maponpaths.
    apply isasetnat.
Qed.
