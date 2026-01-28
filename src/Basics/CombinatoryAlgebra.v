(**

 Combinatory algebras

 Content
 1. Applicative structures
 2. Combinatory algebras
 3. Triviality of combinatory algebras
 4. Derived combinators
 4.1. Identity
 4.2. Constant (second argument)
 4.3. Composition
 4.4. The C-combinator
 4.5. The T-combinator
 4.6. The M-combinator
 4.7. The W-combinator
 4.8. Generalized S-combinator
 4.9. Generalized K-combinator
 5. Lemmas about non-triviality

 *)
Require Import UniMath.MoreFoundations.All.

Declare Scope ca.
Local Open Scope ca.
Delimit Scope ca with ca.

(** * 1. Applicative structures *)
Definition applicative_structure
  : UU
  := ∑ (A : hSet), A → A → A.

Definition make_applicative_structure
           (A : hSet)
           (f : A → A → A)
  : applicative_structure
  := A ,, f.
           
Coercion applicative_structure_to_type
         (A : applicative_structure)
  : hSet
  := pr1 A.

Definition applicative_structure_op
           {A : applicative_structure}
           (a₁ a₂ : A)
  : A
  := pr2 A a₁ a₂.

Notation "a₁ · a₂" := (applicative_structure_op a₁ a₂) : ca.

Proposition app_eq
            {A : applicative_structure}
            {a₁ a₂ b₁ b₂ : A}
            (p : a₁ = b₁)
            (q : a₂ = b₂)
  : a₁ · a₂ = b₁ · b₂.
Proof.
  induction p, q.
  apply idpath.
Qed.

(** * 2. Combinatory algebras *)
Definition combinatory_algebra
  : UU
  := ∑ (A : applicative_structure)
       (k : A)
       (s : A),
     (∏ (a₁ a₂ : A), k · a₁ · a₂ = a₁)
     ×
     (∏ (a₁ a₂ a₃ : A), s · a₁ · a₂ · a₃ = a₁ · a₃ · (a₂ · a₃)).

Definition make_combinatory_algebra
           (A : applicative_structure)
           (k : A)
           (s : A)
           (pk : ∏ (a₁ a₂ : A), k · a₁ · a₂ = a₁)
           (ps : ∏ (a₁ a₂ a₃ : A), s · a₁ · a₂ · a₃ = a₁ · a₃ · (a₂ · a₃))
  : combinatory_algebra
  := A ,, k ,, s ,, pk ,, ps.

Definition make_combinatory_algebra_bckw
           (A : applicative_structure)
           (b : A)
           (c : A)
           (k : A)
           (w : A)
           (pb : ∏ (a₁ a₂ a₃ : A), b · a₁ · a₂ · a₃ = a₁ · (a₂ · a₃))
           (pc : ∏ (a₁ a₂ a₃ : A), c · a₁ · a₂ · a₃ = a₁ · a₃ · a₂)
           (pk : ∏ (a₁ a₂ : A), k · a₁ · a₂ = a₁)
           (pw : ∏ (a₁ a₂ : A), w · a₁ · a₂ = a₁ · a₂ · a₂)
  : combinatory_algebra.
Proof.
  use make_combinatory_algebra.
  - exact A.
  - exact k.
  - exact (b · (b · w) · (b · b · c)).
  - apply pk.
  - abstract
      (intros a₁ a₂ a₃ ;
       rewrite !pb ;
       rewrite pw ;
       rewrite pb ;
       rewrite pc ;
       apply idpath).
Defined.
    
Coercion combinatory_algebra_to_applicative
         (A : combinatory_algebra)
  : applicative_structure
  := pr1 A.

Definition combinatory_algebra_k
           (A : combinatory_algebra)
  : A
  := pr12 A.

Definition combinatory_algebra_s
           (A : combinatory_algebra)
  : A
  := pr122 A.

Notation "'K'" := (combinatory_algebra_k _) : ca.
Notation "'S'" := (combinatory_algebra_s _) : ca.

Proposition combinatory_algebra_k_eq
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : K · a₁ · a₂ = a₁.
Proof.
  exact (pr1 (pr222 A) a₁ a₂).
Defined.

Proposition combinatory_algebra_s_eq
            {A : combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : S · a₁ · a₂ · a₃ = a₁ · a₃ · (a₂ · a₃).
Proof.
  exact (pr2 (pr222 A) a₁ a₂ a₃).
Defined.

(** * 3. Triviality of combinatory algebras *)

(**
   A combinatory algebra is non-trivial if there are two elements which are unequal
 *)
Definition is_non_trivial
           (A : combinatory_algebra)
  : UU
  := ∑ (x y : A), x != y.

Definition is_non_trivial_el
           {A : combinatory_algebra}
           (H : is_non_trivial A)
  : A
  := pr1 H.

Definition is_non_trivial_el'
           {A : combinatory_algebra}
           (H : is_non_trivial A)
  : A
  := pr12 H.

Proposition is_non_trivial_neq
            {A : combinatory_algebra}
            (H : is_non_trivial A)
  : is_non_trivial_el H != is_non_trivial_el' H.
Proof.
  exact (pr22 H).
Defined.

(** * 4. Derived combinators *)

(** ** 4.1. Identity *)
Definition combinatory_algebra_i
           (A : combinatory_algebra)
  : A
  := S · K · K.

Notation "'I'" := (combinatory_algebra_i _) : ca.

Proposition combinatory_algebra_i_eq
            {A : combinatory_algebra}
            (a : A)
  : I · a = a.
Proof.
  unfold combinatory_algebra_i.
  rewrite combinatory_algebra_s_eq.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

(** ** 4.2. Constant (second argument) *)
Definition combinatory_algebra_ks
           (A : combinatory_algebra)
  : A
  := K · I.

Notation "'K*'" := (combinatory_algebra_ks _) : ca.

Proposition combinatory_algebra_ks_eq
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : K* · a₁ · a₂ = a₂.
Proof.
  unfold combinatory_algebra_ks.
  rewrite combinatory_algebra_k_eq.
  rewrite combinatory_algebra_i_eq.
  apply idpath.
Qed.

(** * 4.3. Composition *)
Definition combinatory_algebra_b
           (A : combinatory_algebra)
  : A
  := S · (K · S) · K.

Notation "'B'" := (combinatory_algebra_b _) : ca.

Proposition combinatory_algebra_b_eq
            {A : combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : B · a₁ · a₂ · a₃ = a₁ · (a₂ · a₃).
Proof.
  unfold combinatory_algebra_b.
  rewrite combinatory_algebra_s_eq.
  rewrite combinatory_algebra_k_eq.
  rewrite combinatory_algebra_s_eq.
  rewrite combinatory_algebra_k_eq.
  reflexivity.
Qed.

(** * 4.4. The C-combinator *)
Definition combinatory_algebra_c
           (A : combinatory_algebra)
  : A
  := S · (S · (K · (S · (K · S) · K)) · S) · (K · K).

Notation "'C'" := (combinatory_algebra_c _) : ca.

Proposition combinatory_algebra_c_eq
            {A : combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : C · a₁ · a₂ · a₃ = a₁ · a₃ · a₂.
Proof.
  unfold combinatory_algebra_c.
  do 2 rewrite combinatory_algebra_s_eq.
  rewrite combinatory_algebra_k_eq.
  rewrite combinatory_algebra_s_eq.
  rewrite combinatory_algebra_k_eq.
  rewrite combinatory_algebra_s_eq.
  rewrite combinatory_algebra_k_eq.
  rewrite combinatory_algebra_s_eq.
  do 2 rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

(** ** 4.5. The T-combinator *)
Definition combinatory_algebra_t
           (A : combinatory_algebra)
  : A
  := C · I.

Notation "'T'" := (combinatory_algebra_t _) : ca.

Proposition combinatory_algebra_t_eq
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : T · a₁ · a₂ = a₂ · a₁.
Proof.
  unfold combinatory_algebra_t.
  rewrite combinatory_algebra_c_eq.
  rewrite combinatory_algebra_i_eq.
  apply idpath.
Qed.

(** ** 4.6. The M-combinator *)
Definition combinatory_algebra_m
           (A : combinatory_algebra)
  : A
  := S · I · I.

Notation "'M'" := (combinatory_algebra_m _) : ca.

Proposition combinatory_algebra_m_eq
            {A : combinatory_algebra}
            (a : A)
  : M · a = a · a.
Proof.
  unfold combinatory_algebra_m.
  rewrite combinatory_algebra_s_eq.
  rewrite! combinatory_algebra_i_eq.
  apply idpath.
Qed.

(** ** 4.7. The W-combinator *)
Definition combinatory_algebra_w
           (A : combinatory_algebra)
  : A
  := S · S · (S · K).

Notation "'W'" := (combinatory_algebra_w _) : ca.

Proposition combinatory_algebra_w_eq
            {A : combinatory_algebra}
            (a₁ a₂ : A)
  : W · a₁ · a₂ = a₁ · a₂ · a₂.
Proof.
  unfold combinatory_algebra_w.
  rewrite !combinatory_algebra_s_eq.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

(** ** 4.8. Generalized S-combinator *)
Definition combinatory_algebra_sn
           (A : combinatory_algebra)
           (n : ℕ)
  : A.
Proof.
  destruct n as [ | n ].
  - exact I.
  - induction n as [ | n IHn ].
    + exact S.
    + exact (B · S · (B · IHn)).
Defined.

Notation "'Sn'" := (combinatory_algebra_sn _) : ca.

Proposition combinatory_algebra_sn_Z
            {A : combinatory_algebra}
            (a : A)
  : Sn 0 · a = a.
Proof.
  cbn.
  rewrite combinatory_algebra_i_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_sn_one
            {A : combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : Sn 1 · a₁ · a₂ · a₃ = a₁ · a₃ · (a₂ · a₃).
Proof.
  cbn.
  rewrite combinatory_algebra_s_eq.
  apply idpath.
Qed.

Proposition combinatory_algebra_sn_S
            {A : combinatory_algebra}
            (a₁ a₂ a₃ : A)
            (n : ℕ)
  : Sn (1 + (1 + n)) · a₁ · a₂ · a₃
    =
    Sn (1 + n) · (a₁ · a₃) · (a₂ · a₃).
Proof.
  simpl.
  rewrite combinatory_algebra_b_eq.
  rewrite combinatory_algebra_s_eq.
  rewrite combinatory_algebra_b_eq.
  apply idpath.
Qed.

(** ** 4.9. Generalized K-combinator *)
Definition ca_const
           {A : combinatory_algebra}
           (n : ℕ)
           (a : A)
  : A.
Proof.
  induction n as [ | n IHn ].
  - exact a.
  - exact (K · IHn).
Defined.

Proposition ca_const_Z_eq
            {A : combinatory_algebra}
            (a : A)
  : ca_const 0 a = a.
Proof.
  apply idpath.
Qed.

Proposition ca_const_S_eq'
            {A : combinatory_algebra}
            (n : ℕ)
            (a : A)
  : ca_const (1 + n) a = K · (ca_const n a).
Proof.
  apply idpath.
Qed.

Proposition ca_const_S_eq
            {A : combinatory_algebra}
            (n : ℕ)
            (a b : A)
  : ca_const (1 + n) a · b = ca_const n a.
Proof.
  rewrite ca_const_S_eq'.
  rewrite combinatory_algebra_k_eq.
  apply idpath.
Qed.

(** * 5. Lemmas about non-triviality *)
Proposition is_non_trivial_k_ks
            {A : combinatory_algebra}
            (H : is_non_trivial A)
  : (K : A) != K*.
Proof.
  intro p.
  pose (a₁ := is_non_trivial_el H).
  pose (a₂ := is_non_trivial_el' H).
  assert (K · a₁ · a₂ = K* · a₁ · a₂) as q.
  {
    induction p.
    apply idpath.
  }
  apply (is_non_trivial_neq H).
  rewrite combinatory_algebra_k_eq in q.
  rewrite combinatory_algebra_ks_eq in q.
  exact q.
Qed.        

Proposition is_non_trivial_k_s
            {A : combinatory_algebra}
            (H : is_non_trivial A)
  : (K : A) != S.
Proof.
  intro p.
  assert ((I : A) = K) as q.
  {
    unfold combinatory_algebra_i.
    rewrite <- p.
    rewrite combinatory_algebra_k_eq.
    apply idpath.
  }
  use (is_non_trivial_k_ks H).
  unfold combinatory_algebra_ks.
  rewrite <- q.
  rewrite combinatory_algebra_i_eq.
  apply idpath.
Qed.        
