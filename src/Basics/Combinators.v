(**

 Derived combinators

 In this file, we derive various combinators using combinatory completeness.

 Contents
 1. First projection
 2. Second projection
 3. Pairing
 4. Function pairing
 5. Summing functions
 6. The Y-combinator
 7. The natural numbers
 8. Operations on the natural numbers
 8.1. Successor
 8.2. Predecessor
 8.3. Check whether a number is 0
 8.4. Iteration
 9. Exponentials
 9.1. Evaluation
 9.2. Abstraction
 10. Dependent composition
 11. Combinators for the total space of a dependent assembly
 12. Combinators for dependent sums
 13. Combinators for dependent products

 *)
Require Import UniMath.MoreFoundations.All.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Completeness.

Local Open Scope ca.

(** * 1. First projection *)

(**
   As a λ-term: `λ x . x K`
 *)
Definition combinatory_algebra_pr1
           (A : combinatory_algebra)
  : A
  := Λ (V 0 • Co K).

Notation "'π₁'" := (combinatory_algebra_pr1 _) : ca.

(** * 2. Second projection *)

(**
   As a λ-term: `λ x . x K*`
 *)
Definition combinatory_algebra_pr2
           (A : combinatory_algebra)
  : A
  := Λ (V 0 • Co K*).

Notation "'π₂'" := (combinatory_algebra_pr2 _) : ca.

(** * 3. Pairing *)

(**
   As a λ-term: `λ x y z . z x y`
 *)
Definition combinatory_algebra_pair
           (A : combinatory_algebra)
  : A
  := Λ (V 2 • V 0 • V 1).

Notation "'pair'" := (combinatory_algebra_pair _) : ca.

Proposition combinatory_algebra_pr1_pair
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : π₁ · (pair · a₁ · a₂) = a₁.
Proof.
  unfold combinatory_algebra_pr1, ca_abs.
  rewrite lam_term_single.
  simpl.
  unfold combinatory_algebra_pair, ca_abs.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_pr2_pair
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : π₂ · (pair · a₁ · a₂) = a₂.
Proof.
  unfold combinatory_algebra_pr2, ca_abs.
  rewrite lam_term_single.
  simpl.
  unfold combinatory_algebra_pair, ca_abs.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite combinatory_algebra_ks_eq.
  apply idpath.
Qed.

Definition combinatory_algebra_pair_swap
           (A : combinatory_algebra)
  : A
  := Λ (V 2 • V 1 • V 0).

Notation "'pair_s'" := (combinatory_algebra_pair_swap _) : ca.

Proposition combinatory_algebra_pr1_pair_s
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : π₁ · (pair_s · a₁ · a₂) = a₂.
Proof.
  unfold combinatory_algebra_pr1, ca_abs.
  rewrite lam_term_single.
  simpl.
  unfold combinatory_algebra_pair, ca_abs.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_pr2_pair_s
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : π₂ · (pair_s · a₁ · a₂) = a₁.
Proof.
  unfold combinatory_algebra_pr2, ca_abs.
  rewrite lam_term_single.
  simpl.
  unfold combinatory_algebra_pair, ca_abs.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite combinatory_algebra_ks_eq.
  apply idpath.
Qed.

(** * 4. Function pairing *)

(**
   As a λ-term: `λ f g b z . z (f z) (g z)`
 *)
Definition combinatory_algebra_pair_fun
           (A : combinatory_algebra)
  : A
  := Λ (V 3 • (V 0 • V 2) • (V 1 • V 2)).

Notation "'pairf'" := (combinatory_algebra_pair_fun _) : ca.

Proposition combinatory_algebra_pr1_pair_fun
            {A : combinatory_algebra}
            (a₁ a₂ b : A)
  : π₁ · (pairf · a₁ · a₂ · b) = a₁ · b.
Proof.
  unfold combinatory_algebra_pr1, ca_abs.
  rewrite lam_term_single.
  simpl.
  unfold combinatory_algebra_pair, ca_abs.
  etrans.
  {
    do 3 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite !lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_pr2_pair_fun
            {A : combinatory_algebra}
            (a₁ a₂ b : A)
  : π₂ · (pairf · a₁ · a₂ · b) = a₂ · b.
Proof.
  unfold combinatory_algebra_pr2, ca_abs.
  rewrite lam_term_single.
  simpl.
  unfold combinatory_algebra_pair, ca_abs.
  etrans.
  {
    do 3 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite !lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite combinatory_algebra_ks_eq.
  apply idpath.
Qed.

(** * 5. Summing functions *)

(**
   As a λ-term: `λ f g b . (π₁ b) (f (π₂ b)) (g (π₂ b))`

   This λ-term might look odd at first. The main idea is that a coproduct is represented
   by a product: the first coordinate indicates the component and the second coordinate
   indicates the actual value. Specifically, if `π₁ b` is `K`, then it returns `f (π₂ b)`,
   and if `π₂ b` is `K*`, then it returns `g (π₂ b)`.
 *)
Definition combinatory_algebra_sum_fun
           (A : combinatory_algebra)
  : A
  := let b := V 2 in
     Λ ((Co π₁ • b) • (V 0 • (Co π₂ • b)) • (V 1 • (Co π₂ • b))).

Notation "'sumf'" := (combinatory_algebra_sum_fun _) : ca.

Proposition combinatory_algebra_sum_fun_inl
            {A : combinatory_algebra}
            (a₁ a₂ b : A)
            (p : π₁ · b = K)
  : sumf · a₁ · a₂ · b = a₁ · (π₂ · b).
Proof.
  unfold combinatory_algebra_sum_fun, ca_abs.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite p.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_sum_fun_inr
            {A : combinatory_algebra}
            (a₁ a₂ b : A)
            (p : π₁ · b = K*)
  : sumf · a₁ · a₂ · b = a₂ · (π₂ · b).
Proof.
  unfold combinatory_algebra_sum_fun, ca_abs.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite p.
  rewrite combinatory_algebra_ks_eq.
  apply idpath.
Qed.

Definition combinatory_algebra_sum_fun_fib
           (A : combinatory_algebra)
  : A
  := let b := V 3 in
     Λ ((Co π₁ • b) • (V 0 • V 2 • (Co π₂ • b)) • (V 1 • V 2 • (Co π₂ • b))).

Notation "'sumf_fib'" := (combinatory_algebra_sum_fun_fib _) : ca.

Proposition combinatory_algebra_sum_fun_fib_inl
            {A : combinatory_algebra}
            (a₁ a₂ b₁ b₂ : A)
            (p : π₁ · b₂ = K)
  : sumf_fib · a₁ · a₂ · b₁ · b₂ = a₁ · b₁ · (π₂ · b₂).
Proof.
  unfold combinatory_algebra_sum_fun, ca_abs.
  etrans.
  {
    do 3 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite !lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite p.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_sum_fun_fib_inr
            {A : combinatory_algebra}
            (a₁ a₂ b₁ b₂ : A)
            (p : π₁ · b₂ = K*)
  : sumf_fib · a₁ · a₂ · b₁ · b₂ = a₂ · b₁ · (π₂ · b₂).
Proof.
  unfold combinatory_algebra_sum_fun, ca_abs.
  etrans.
  {
    do 3 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite !lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  rewrite p.
  rewrite combinatory_algebra_ks_eq.
  apply idpath.
Qed.

(** * 6. The Y-combinator *)

(**
   As a λ-term: `λ f . (λ x . f (x x)) (λ x . f (x x))`

   There is a challenge in defining the Y-combinator. This is because we proved a
   version of combinatory completeness that binds all free variables in a term rather
   than some of them. For this reason, we take a small detour. We first define the
   following λ-term: `λ f x . f (x x)`, which we call `Yy`. Then the `Y` combinator
   is defined to be `λ f . M (Yy f)` where we use that `M x = x x`.
 *)
Definition combinatory_algebra_y_help
           (A : combinatory_algebra)
  : A
  := Λ (V 0 • (V 1 • V 1)).

Notation "'Yy'" := (combinatory_algebra_y_help _) : ca.

Definition combinatory_algebra_y
           (A : combinatory_algebra)
  : A
  := Λ (Co M • (Co Yy • V 0)).

Notation "'Y'" := (combinatory_algebra_y _) : ca.

Proposition combinatory_algebra_y_eq
            {A : combinatory_algebra}
            (a : A)
  : Y · a = a · (Y · a).
Proof.
  unfold combinatory_algebra_y.
  etrans.
  {
    apply lam_term_single.
  }
  simpl.
  rewrite combinatory_algebra_m_eq.
  etrans.
  {
    apply maponpaths_2.
    unfold combinatory_algebra_y_help.
    apply lam_term_multiple.
  }
  rewrite lam_term_single.
  simpl.
  apply maponpaths.
  refine (!_).
  etrans.
  {
    apply lam_term_single.
  }
  simpl.
  rewrite combinatory_algebra_m_eq.
  apply idpath.
Qed.

(** * 7. The natural numbers *)
Definition combinatory_algebra_nat
           (A : combinatory_algebra)
           (n : ℕ)
  : A.
Proof.
  induction n as [ | n IHn ].
  - exact I.
  - exact (pair · K* · IHn).
Defined.

Notation "⌜ n ⌝" := (combinatory_algebra_nat _ n) : ca. (* \c1 \c2 *)

Proposition combinatory_algebra_nat_Z
            (A : combinatory_algebra)
  : ⌜ 0 ⌝ = (I : A).
Proof.
  apply idpath.
Qed.

Proposition combinatory_algebra_nat_succ
            (A : combinatory_algebra)
            (n : ℕ)
  : ⌜ 1 + n ⌝ = (pair : A) · K* · ⌜ n ⌝.
Proof.
  apply idpath.
Qed.

(**
   In a non-trivial combinatory algebra, zero and successors are unequal.
 *)
Proposition combinatory_algebra_nat_Z_succ_neq
            {A : combinatory_algebra}
            (H : is_non_trivial A)
            (n : ℕ)
  : (⌜ 0 ⌝ : A) != ⌜ 1 + n ⌝.
Proof.
  intro p.
  use (is_non_trivial_k_ks H).
  refine (_ @ maponpaths (λ z, π₁ · z) p @ _).
  - simpl.
    refine (!_).
    etrans.
    {
      apply lam_term_single.
    }
    simpl.
    rewrite combinatory_algebra_i_eq.
    apply idpath.
  - simpl.
    rewrite combinatory_algebra_pr1_pair.
    apply idpath.
Qed.
            
(** * 8. Operations on the natural numbers *)

(** * 8.1. Successor *)
Definition combinatory_algebra_succ
           (A : combinatory_algebra)
  : A
  := pair · K*.

Notation "'succ'" := (combinatory_algebra_succ _) : ca.

Proposition combinatory_algebra_succ_eq
            {A : combinatory_algebra}
            (n : ℕ)
  : (succ : A) · ⌜ n ⌝ = ⌜ 1 + n ⌝.
Proof.
  unfold combinatory_algebra_succ.
  apply idpath.
Qed.

(** * 8.2. Predecessor *)
Definition combinatory_algebra_pred
           (A : combinatory_algebra)
  : A
  := π₂.

Notation "'pred'" := (combinatory_algebra_pred _) : ca.

Proposition combinatory_algebra_pred_eq
            {A : combinatory_algebra}
            (n : ℕ)
  : (pred : A) · ⌜ 1 + n ⌝ = ⌜ n ⌝.
Proof.
  unfold combinatory_algebra_pred.
  simpl.
  rewrite combinatory_algebra_pr2_pair.
  apply idpath.
Qed.

(** * 8.3. Check whether a number is 0 *)
Definition combinatory_algebra_zero
           (A : combinatory_algebra)
  : A
  := π₁.

Notation "'zero'" := (combinatory_algebra_zero _) : ca.

Proposition combinatory_algebra_zero_Z
            (A : combinatory_algebra)
  : (zero : A) · ⌜ 0 ⌝ = K.
Proof.
  unfold combinatory_algebra_zero.
  simpl.
  unfold combinatory_algebra_pr1.
  etrans.
  {
    apply lam_term_single.
  }
  simpl.
  rewrite combinatory_algebra_i_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_zero_succ
            {A : combinatory_algebra}
            (n : ℕ)
  : (zero : A) · ⌜ 1 + n ⌝ = K*.
Proof.
  unfold combinatory_algebra_zero.
  simpl.
  rewrite combinatory_algebra_pr1_pair.
  apply idpath.
Qed.

#[local] Opaque combinatory_algebra_nat.

(** * 8.4. Iteration *)
Definition combinatory_algebra_iter_help
           {A : combinatory_algebra}
           (z s : A)
  : A
  := let f := V 0 in
     let n := V 1 in
     Λ ((Co zero • n) • Co z • (Co s • (f • (Co pred • n)))).

Proposition combinatory_algebra_iter_help_zero
            {A : combinatory_algebra}
            (z s f : A)
  : combinatory_algebra_iter_help z s · f · ⌜ 0 ⌝ = z.
Proof.
  unfold combinatory_algebra_iter_help.
  etrans.
  {
    apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_single.
  simpl.
  rewrite combinatory_algebra_zero_Z.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_iter_help_succ
            {A : combinatory_algebra}
            (z s f : A)
            (n : ℕ)
  : combinatory_algebra_iter_help z s · f · ⌜ 1 + n ⌝ = s · (f · ⌜ n ⌝).
Proof.
  unfold combinatory_algebra_iter_help.
  etrans.
  {
    apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_single.
  simpl.
  rewrite combinatory_algebra_zero_succ.
  rewrite combinatory_algebra_ks_eq.
  rewrite combinatory_algebra_pred_eq.
  apply idpath.
Qed.

Definition combinatory_algebra_iter
           {A : combinatory_algebra}
           (z s : A)
  : A
  := Y · combinatory_algebra_iter_help z s.

Proposition combinatory_algebra_iter_Z
            {A : combinatory_algebra}
            (z s : A)
  : combinatory_algebra_iter z s · ⌜ 0 ⌝ = z.
Proof.
  unfold combinatory_algebra_iter.
  rewrite combinatory_algebra_y_eq.
  fold (combinatory_algebra_iter z s).
  rewrite combinatory_algebra_iter_help_zero.
  apply idpath.
Qed.

Proposition combinatory_algebra_iter_succ
            {A : combinatory_algebra}
            (z s : A)
            (n : ℕ)
  : combinatory_algebra_iter z s · ⌜ 1 + n ⌝
    =
    s · (combinatory_algebra_iter z s · ⌜ n ⌝).
Proof.
  etrans.
  {
    unfold combinatory_algebra_iter.
    rewrite combinatory_algebra_y_eq.
    fold (combinatory_algebra_iter z s).
    apply idpath.
  }
  rewrite combinatory_algebra_iter_help_succ.
  apply idpath.
Qed.

(** * 9. Exponentials *)

(** * 9.1. Evaluation *)
Definition combinatory_algebra_eval
           (A : combinatory_algebra)
  : A
  := Λ (Co π₂ • V 0 • (Co π₁ • V 0)).

Notation "'ε'" := (combinatory_algebra_eval _) : ca.

Proposition combinatory_algebra_eval_eq
            {A : combinatory_algebra}
            (a : A)
  : ε · a = π₂ · a · (π₁ · a).
Proof.
  unfold combinatory_algebra_eval.
  etrans.
  {
    apply lam_term_single.
  }
  simpl.
  apply idpath.
Qed.

(** * 9.2. Abstraction *)
Definition combinatory_algebra_lam
           (A : combinatory_algebra)
  : A
  := Λ (V 0 • (Co pair • V 2 • V 1)).

Notation "'lam'" := (combinatory_algebra_lam _).

Proposition combinatory_algebra_lam_eq
            {A : combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : lam · a₁ · a₂ · a₃
    =
    a₁ · (pair · a₃ · a₂).
Proof.
  unfold combinatory_algebra_lam.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

(** * 10. Dependent composition *)
Definition combinatory_algebra_d_comp
           (A : combinatory_algebra)
  : A
  := Λ (V 0 • (V 2 • V 3) • (V 1 • V 3 • V 4)).

Notation "'Bd'" := (combinatory_algebra_d_comp _) : ca.

Proposition combinatory_algebra_d_comp_eq
            {A : combinatory_algebra}
            (a₁ a₂ a₃ a₄ a₅ : A)
  : Bd · a₁ · a₂ · a₃ · a₄ · a₅ = a₁ · (a₃ · a₄) · (a₂ · a₄ · a₅).
Proof.
  unfold combinatory_algebra_d_comp.
  etrans.
  {
    do 4 apply maponpaths_2.
    apply lam_term_multiple.
  }
  etrans.
  {
    do 3 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite !lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

(** * 11. Combinators for the total space of a dependent assembly *)
Definition combinatory_algebra_total_comp
           (A : combinatory_algebra)
  : A
  := Λ (V 0 • (Co π₁ • V 1) • (Co π₂ • V 1)).

Notation "'Bt'" := (combinatory_algebra_total_comp _) : ca.

Proposition combinatory_algebra_total_comp_eq
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : Bt · a₁ · a₂ = a₁ · (π₁ · a₂) · (π₂ · a₂).
Proof.
  unfold combinatory_algebra_total_comp.
  etrans.
  {
    apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

Definition combinatory_algebra_total_mor_tm
           (A : combinatory_algebra)
  : A
  := Λ (Co π₂ • (V 0 • (Co pair • V 1 • V 2))).

Notation "'Ft'" := (combinatory_algebra_total_mor_tm _) : ca.

Proposition combinatory_algebra_total_mor_eq
            {A : combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : Ft · a₁ · a₂ · a₃ = π₂ · (a₁ · (pair · a₂ · a₃)).
Proof.
  unfold combinatory_algebra_total_mor_tm.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

(** * 12. Combinators for dependent sums *)
Definition combinatory_algebra_dep_sum_pr
           (A : combinatory_algebra)
  : A
  := Λ (V 0 • (Co π₁ • V 2) • (Co π₂ • V 2)).

Notation "'dep_π'" := (combinatory_algebra_dep_sum_pr _) : ca.

Proposition combinatory_algebra_dep_sum_pr_eq
            {A : combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : dep_π · a₁ · a₂ · a₃
    =
    a₁ · (π₁ · a₃) · (π₂ · a₃).
Proof.
  unfold combinatory_algebra_dep_sum_pr.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

Definition combinatory_algebra_dep_sum_stable
           (A : combinatory_algebra)
  : A
  := Λ (Co pair • (Co π₁ • (Co π₁ • V 1)) • (Co π₂ • V 1)).

Notation "'sum_s'" := (combinatory_algebra_dep_sum_stable _) : ca.

Proposition combinatory_algebra_dep_sum_stable_eq
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : sum_s · a₁ · a₂ = pair · (π₁ · (π₁ · a₂)) · (π₂ · a₂).
Proof.
  unfold combinatory_algebra_dep_sum_stable.
  etrans.
  {
    apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

Definition combinatory_algebra_dep_sum_stable_inv
           (A : combinatory_algebra)
  : A
  := Λ (Co pair • (Co pair • (Co π₁ • V 1) • (V 0)) • (Co π₂ • V 1)).

Notation "'sum_si'" := (combinatory_algebra_dep_sum_stable_inv _) : ca.

Proposition combinatory_algebra_dep_sum_stable_inv_eq
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : sum_si · a₁ · a₂ = pair · (pair · (π₁ · a₂) · a₁) · (π₂ · a₂).
Proof.
  unfold combinatory_algebra_dep_sum_stable.
  etrans.
  {
    apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

Definition combinatory_algebra_dep_sum_stable_strong
           (A : combinatory_algebra)
  : A
  := Λ (Co pair • (Co π₁ • (Co π₂ • V 0)) • (Co π₂ • (Co π₂ • V 0))).

Notation "'sum_str'" := (combinatory_algebra_dep_sum_stable_strong _) : ca.

Proposition combinatory_algebra_dep_sum_stable_strong_eq
            {A : combinatory_algebra}
            (a : A)
  : sum_str · a = pair · (π₁ · (π₂ · a)) · (π₂ · (π₂ · a)).
Proof.
  unfold combinatory_algebra_dep_sum_stable_strong.
  etrans.
  {
    apply lam_term_single.
  }
  simpl.
  apply idpath.
Qed.

(** * 13. Combinators for dependent products *)
Definition combinatory_algebra_dep_lam
           (A : combinatory_algebra)
  : A
  := Λ (V 0 • V 3 • V 2).

Notation "'lam_d'" := (combinatory_algebra_dep_lam _) : ca.

Proposition combinatory_algebra_dep_lam_eq
            {A : combinatory_algebra}
            (a₁ a₂ a₃ a₄ : A)
  : lam_d · a₁ · a₂ · a₃ · a₄ = a₁ · a₄ · a₃.
Proof.
  unfold combinatory_algebra_dep_sum_stable.
  etrans.
  {
    do 3 apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite !lam_term_multiple.
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

Definition combinatory_algebra_tm_fun
           (A : combinatory_algebra)
  : A
  := Λ (Co pair • V 1 • (V 0 • V 1)).

Notation "'tm_t'" := (combinatory_algebra_tm_fun _).

Proposition combinatory_algebra_tm_fun_eq
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : tm_t · a₁ · a₂ = pair · a₂ · (a₁ · a₂).
Proof.
  unfold combinatory_algebra_tm_fun.
  etrans.
  {
    apply maponpaths_2.
    apply lam_term_multiple.
  }
  rewrite lam_term_single.
  simpl.
  apply idpath.
Qed.

#[global] Opaque "π₁" "π₂" "pair".
