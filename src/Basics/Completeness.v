(**

 Combinatory completeness of combinatory algebras

 Contents
 1. Variables
 2. Terms
 3. Well-scopedness of terms
 4. Preliminaries for combinatory completeness
 5. Combinatory completeness

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Topology.Prelim.
Require Import Basics.CombinatoryAlgebra.

Local Open Scope ca.

(** * 1. Variables *)
Definition var (n : ℕ) : UU := ∑ (m : ℕ), m < n.

Definition make_var {n : ℕ} (m : ℕ) (p : m < n) : var n := m ,, p.

Coercion var_to_nat {n : ℕ} (v : var n) : ℕ := pr1 v.

Definition var_lt {n : ℕ} (v : var n) : v < n := pr2 v.

Definition var_zero (n : ℕ) : var (1 + n).
Proof.
  use make_var.
  - exact 0.
  - abstract
      (cbn ; apply idpath).
Defined.

Definition var_suc {n : ℕ} (v : var n) : var (1 + n).
Proof.
  use make_var.
  - exact (1 + v).
  - abstract
      (use natlthandplusl ;
       apply var_lt).
Defined.

(** * 2. Terms *)

(**
   Note that we represent variables as De Bruijn indices
 *)
Inductive term (A : combinatory_algebra) : UU :=
| var_tm : ℕ → term A
| const : A → term A
| app : term A → term A → term A.

Arguments var_tm {A} _.
Arguments const {A} _.
Arguments app {A} _ _.

Notation "'V'" := var_tm : ca.
Notation "'Co'" := const : ca.

Notation "t₁ • t₂" := (app t₁ t₂) (at level 40, left associativity) : ca. (* \bu 2 *)

Definition term_subst
           {A : combinatory_algebra}
           (t : term A)
           (c : A)
  : term A.
Proof.
  induction t as [ n | ca | t₁ IHt₁ t₂ IHt₂ ].
  - induction n as [ | n IHn ].
    + exact (Co c).
    + exact (V n).
  - exact (Co ca).
  - exact (IHt₁ • IHt₂).
Defined.

Notation "t '{{' c '}}'" := (term_subst t c) : ca.

(** * 3. Well-scopedness of terms *)

(**
   Terms may contain free variables. A term is well-scoped with respect to a natural number
   if every variable is smaller than that natural number. The natural number indicates the
   context of the term by indicating the number of free variables.
 *)
Definition is_well_scoped
           {A : combinatory_algebra}
           (t : term A)
           (n : ℕ)
  : hProp.
Proof.
  induction t as [ m | ca | t₁ IHt₁ t₂ IHt₂ ].
  - exact (m < n).
  - exact htrue.
  - exact (IHt₁ ∧ IHt₂).
Defined.

Proposition is_well_scoped_weaken
            {A : combinatory_algebra}
            (t : term A)
            {n n' : ℕ}
            (p : n ≤ n')
            (q : is_well_scoped t n)
  : is_well_scoped t n'.
Proof.
  induction t as [ m | ca | t₁ IHt₁ t₂ IHt₂ ].
  - exact (natlthlehtrans _ _ _ q p).
  - cbn -[natlth] in *.
    exact tt.
  - simpl ; simpl in q.
    split.
    + apply IHt₁.
      exact (pr1 q).
    + apply IHt₂.
      exact (pr2 q).
Qed.

Definition tm_subst_var
           {A : combinatory_algebra}
           (t : term A)
           (c : A)
           (Ht : is_well_scoped t 1)
  : A.
Proof.
  induction t as [ n | ca | t₁ IHt₁ t₂ IHt₂ ].
  - induction n as [ | n IHn ].
    + exact c.
    + apply fromempty.
      exact (negnatlthn0 0 Ht).
  - exact ca.
  - exact (IHt₁ (pr1 Ht) · IHt₂ (pr2 Ht)).
Defined.

Proposition is_open_tm_subst
            {A : combinatory_algebra}
            (t : term A)
            {n : ℕ}
            (Ht : is_well_scoped t (1 + n))
            (a : A)
  : is_well_scoped (t {{ a }}) n.
Proof.
  induction t as [ m | ca | t₁ IHt₁ t₂ IHt₂ ].
  - induction m as [ | l IHl ].
    + simpl.
      apply tt.
    + exact Ht.
  - exact tt.
  - split.
    + apply IHt₁.
      apply Ht.
    + apply IHt₂.
      apply Ht.
Qed.

(**
   Every term is well-scoped in a large enough context
 *)
Definition max_var
           {A : combinatory_algebra}
           (t : term A)
  : ℕ.
Proof.
  induction t as [ n | ca | t₁ IHt₁ t₂ IHt₂ ].
  - exact n.
  - exact 0.
  - exact (max IHt₁ IHt₂).
Defined.

Proposition is_well_scoped_max
            {A : combinatory_algebra}
            (t : term A)
  : is_well_scoped t (max_var t + 1).
Proof.
  induction t as [ n | ca | t₁ IHt₁ t₂ IHt₂ ].
  - cbn -[natlth].
    exact (natltplusS 0 n).
  - cbn -[natlth].
    exact tt.
  - simpl.
    split ; cbn -[natlth].
    + refine (is_well_scoped_weaken _ _ IHt₁).
      use natlehandplusr.
      apply max_le_l.
    + refine (is_well_scoped_weaken _ _ IHt₂).
      use natlehandplusr.
      apply max_le_r.
Qed.

(** 4. Preliminaries for combinatory completeness *)

(**
   We first give a term that picks a specified argument. More specifically, we give an
   element `a_i` in a combinatory algebra such that `a_i · x_1 · ... · x_n = x_i`. This
   element is called [ca_var].
 *)
Definition ca_var_zero_S
           (A : combinatory_algebra)
           (n : ℕ)
  : A.
Proof.
  destruct n as [ | n ].
  - exact I.
  - induction n as [ | n IHn ].
    + exact K.
    + exact (B · K · IHn).
Defined.

Proposition ca_var_zero_S_Z
            {A : combinatory_algebra}
            (a : A)
  : ca_var_zero_S A 0 · a = a.
Proof.
  cbn.
  rewrite combinatory_algebra_i_eq.
  apply idpath.
Qed.

Proposition ca_var_zero_S_one
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : ca_var_zero_S A 1 · a₁ · a₂ = a₁.
Proof.
  cbn.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

Proposition ca_var_zero_S_S
            {A : combinatory_algebra}
            (a₁ a₂ : A)
            (n : ℕ)
  : ca_var_zero_S A (1 + (1 + n)) · a₁ · a₂
    =
    ca_var_zero_S A (1 + n) · a₁.
Proof.
  simpl.
  rewrite combinatory_algebra_b_eq.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

Proposition ca_var_zero_S_S'
            {A : combinatory_algebra}
            (a₁ : A)
            (n : ℕ)
  : ca_var_zero_S A (1 + (1 + n)) · a₁
    =
    K · (ca_var_zero_S A (1 + n) · a₁).
Proof.
  simpl.
  rewrite combinatory_algebra_b_eq.
  apply idpath.
Qed.

Definition ca_var_zero
           (A : combinatory_algebra)
           (n : ℕ)
           (p : 0 < n)
  : A.
Proof.
  induction n as [ | n IHn ].
  - apply fromempty.
    exact (negnatlthn0 _ p).
  - exact (ca_var_zero_S A n).
Defined.

Proposition ca_var_zero_succ
            {A : combinatory_algebra}
            (n : ℕ)
            (p : 0 < 1 + n)
  : ca_var_zero A (1 + n) p = ca_var_zero_S A n.
Proof.
  apply idpath.
Qed.

Definition ca_var'
           {A : combinatory_algebra}
           {n : ℕ}
           (m : ℕ)
           (p : m < n)
  : A.
Proof.
  revert n p.
  induction m as [ | m IHm ] ; intros n p.
  - exact (ca_var_zero A n p).
  - induction n as [ | n IHn ].
    + apply fromempty.
      exact (negnatlthn0 _ p).
    + refine (C · K* · IHm n _).
      apply p.
Defined.

Definition ca_var
           {A : combinatory_algebra}
           {n : ℕ}
           (v : var n)
  : A.
Proof.
  induction v as [ m p ].
  exact (ca_var' m p).
Defined.

Proposition ca_var_zero_eq
            (A : combinatory_algebra)
            (n : ℕ)
  : ca_var (var_zero n) = ca_var_zero_S A n.
Proof.
  apply idpath.
Qed.

Proposition ca_var_zero_eq_Z
            {A : combinatory_algebra}
            (a : A)
  : ca_var (var_zero 0) · a = a.
Proof.
  rewrite ca_var_zero_eq.
  rewrite ca_var_zero_S_Z.
  apply idpath.
Qed.

Proposition ca_var_zero_eq_one
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : ca_var (var_zero 1) · a₁ · a₂ = a₁.
Proof.
  rewrite ca_var_zero_eq.
  rewrite ca_var_zero_S_one.
  apply idpath.
Qed.

Proposition ca_var_zero_eq_succ
            {A : combinatory_algebra}
            (a₁ a₂ : A)
            (n : ℕ)
  : ca_var (var_zero (1 + (1 + n))) · a₁ · a₂
    =
    ca_var (var_zero (1 + n)) · a₁.
Proof.
  rewrite !ca_var_zero_eq.
  rewrite ca_var_zero_S_S.
  apply idpath.
Qed.

Proposition ca_var_s
            {A : combinatory_algebra}
            {n : ℕ}
            (v : var n)
            (a : A)
  : ca_var (var_suc v) · a = ca_var v.
Proof.
  unfold ca_var.
  simpl.
  rewrite combinatory_algebra_c_eq.
  rewrite combinatory_algebra_ks_eq.
  induction v as [ m p ].
  simpl.
  refine (maponpaths (ca_var' m) _).
  apply propproperty.
Qed.

(** * 5. Combinatory completeness *)
Definition lam_term
           {A : combinatory_algebra}
           (t : term A)
           {n : ℕ}
           (Ht : is_well_scoped t n)
  : A.
Proof.
  induction t as [ m | ca | t₁ IHt₁ t₂ IHt₂ ].
  - exact (ca_var (make_var m Ht)).
  - exact (ca_const n ca).
  - exact (Sn n · IHt₁ (pr1 Ht) · IHt₂ (pr2 Ht)).
Defined.

Proposition lam_term_single
            {A : combinatory_algebra}
            (t : term A)
            (Ht : is_well_scoped t 1)
            (a : A)
  : lam_term t Ht · a = tm_subst_var t a Ht.
Proof.
  induction t as [ n | ca | t₁ IHt₁ t₂ IHt₂ ].
  - assert (0 = n) as p.
    {
      refine (!_).
      cbn -[natlth] in Ht.
      apply natlth1tois0.
      exact Ht.
    }
    induction p.
    cbn.
    apply combinatory_algebra_i_eq.
  - simpl.
    rewrite combinatory_algebra_k_eq.
    apply idpath.
  - simpl.
    rewrite combinatory_algebra_s_eq.
    rewrite IHt₁.
    rewrite IHt₂.
    apply idpath.
Qed.

Proposition lam_term_multiple
            {A : combinatory_algebra}
            (t : term A)
            {n : ℕ}
            (Ht : is_well_scoped t (1 + (1 + n)))
            (a : A)
  : lam_term t Ht · a = lam_term (t {{ a }}) (is_open_tm_subst t Ht a).
Proof.
  induction t as [ m | ca | t₁ IHt₁ t₂ IHt₂ ].
  - destruct m as [ | m ] ; simpl.
    + induction n as [ | n IHn ].
      * cbn.
        apply idpath.
      * rewrite ca_const_S_eq'.
        cbn -[ca_var_zero_S].
        rewrite ca_var_zero_S_S'.
        apply maponpaths.
        refine (IHn _).
        apply Ht.
    + cbn.
      rewrite combinatory_algebra_c_eq.
      rewrite combinatory_algebra_ks_eq.
      apply maponpaths.
      apply (propproperty _ Ht).
  - simpl.
    rewrite combinatory_algebra_k_eq.
    apply idpath.
  - simpl.
    rewrite combinatory_algebra_b_eq.
    rewrite combinatory_algebra_s_eq.
    rewrite combinatory_algebra_b_eq.
    rewrite IHt₁.
    rewrite IHt₂.
    use app_eq.
    + do 2 apply maponpaths.
      apply propproperty.
    + apply maponpaths.
      apply propproperty.
Qed.    

(**
   The following is a convenient way to use combinatory completeness. This is because
   one does not need to worry about well-scopedness.
 *)
Definition ca_abs
           {A : combinatory_algebra}
           (t : term A)
  : A
  := lam_term t (is_well_scoped_max t).

Notation "'Λ' t" := (ca_abs t) (at level 200).
