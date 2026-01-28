(**

 Linear combinatory algebras

 Contents
 1. Linear combinatory algebras
 2. Derived combinators
 3. The combinatory algebra associated to a linear combinatory algebra

 *)
Require Import UniMath.MoreFoundations.All.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.

Declare Scope lca.
Local Open Scope lca.
Delimit Scope lca with lca.

Notation "a₁ · a₂" := (applicative_structure_op a₁ a₂) : lca.

(** * 1. Linear combinatory algebras *)
Definition linear_combinatory_algebra
  : UU
  := ∑ (A : applicative_structure)
       (exc : A → A)
       (i b c k w d del f : A),
     (∏ (a : A), i · a = a)
     ×
     (∏ (a₁ a₂ a₃ : A), b · a₁ · a₂ · a₃ = a₁ · (a₂ · a₃))
     ×
     (∏ (a₁ a₂ a₃ : A), c · a₁ · a₂ · a₃ = a₁ · a₃ · a₂)
     ×
     (∏ (a₁ a₂ : A), k · a₁ · (exc a₂) = a₁)
     ×
     (∏ (a₁ a₂ : A), w · a₁ · (exc a₂) = a₁ · (exc a₂) · (exc a₂))
     ×
     (∏ (a : A), d · (exc a) = a)
     ×
     (∏ (a : A), del · (exc a) = exc (exc a))
     ×
     (∏ (a₁ a₂ : A), f · (exc a₁) · (exc a₂) = exc (a₁ · a₂)).

Definition make_linear_combinatory_algebra
           (A : applicative_structure)
           (exc : A → A)
           (i b c k w d del f : A)
           (pi : ∏ (a : A), i · a = a)
           (pb : ∏ (a₁ a₂ a₃ : A), b · a₁ · a₂ · a₃ = a₁ · (a₂ · a₃))
           (pc : ∏ (a₁ a₂ a₃ : A), c · a₁ · a₂ · a₃ = a₁ · a₃ · a₂)
           (pk : ∏ (a₁ a₂ : A), k · a₁ · (exc a₂) = a₁)
           (pw : ∏ (a₁ a₂ : A), w · a₁ · (exc a₂) = a₁ · (exc a₂) · (exc a₂))
           (pd : ∏ (a : A), d · (exc a) = a)
           (pdel : ∏ (a : A), del · (exc a) = exc (exc a))
           (pf : ∏ (a₁ a₂ : A), f · (exc a₁) · (exc a₂) = exc (a₁ · a₂))
  : linear_combinatory_algebra
  := A ,, exc ,, i ,, b ,, c ,, k ,, w ,, d ,, del ,, f
     ,, pi ,, pb ,, pc ,, pk ,, pw ,, pd ,, pdel ,, pf.

Coercion linear_combinatory_algebra_to_structure
         (A : linear_combinatory_algebra)
  : applicative_structure
  := pr1 A.

Definition linear_combinatory_algebra_exc
           {A : linear_combinatory_algebra}
           (a : A)
  : A
  := pr12 A a.

Notation "! a" := (linear_combinatory_algebra_exc a) : lca.

Definition linear_combinatory_algebra_i
           (A : linear_combinatory_algebra)
  : A
  := pr122 A.

Notation "'I'" := (linear_combinatory_algebra_i _) : lca.

Proposition linear_combinatory_algebra_i_eq
            {A : linear_combinatory_algebra}
            (a : A)
  : I · a = a.
Proof.
  exact (pr12 (pr222 (pr222 (pr222 A))) a).
Defined.

Definition linear_combinatory_algebra_b
           (A : linear_combinatory_algebra)
  : A
  := pr1 (pr222 A).

Notation "'B'" := (linear_combinatory_algebra_b _) : lca.

Proposition linear_combinatory_algebra_b_eq
            {A : linear_combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : B · a₁ · a₂ · a₃ = a₁ · (a₂ · a₃).
Proof.
  exact (pr122 (pr222 (pr222 (pr222 A))) a₁ a₂ a₃).
Defined.

Definition linear_combinatory_algebra_c
           (A : linear_combinatory_algebra)
  : A
  := pr12 (pr222 A).

Notation "'C'" := (linear_combinatory_algebra_c _) : lca.

Proposition linear_combinatory_algebra_c_eq
            {A : linear_combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : C · a₁ · a₂ · a₃ = a₁ · a₃ · a₂.
Proof.
  exact (pr1 (pr222 (pr222 (pr222 (pr222 A)))) a₁ a₂ a₃).
Defined.

Definition linear_combinatory_algebra_k
           (A : linear_combinatory_algebra)
  : A
  := pr122 (pr222 A).

Notation "'K'" := (linear_combinatory_algebra_k _) : lca.

Proposition linear_combinatory_algebra_k_eq
            {A : linear_combinatory_algebra}
            (a₁ a₂ : A)
  : K · a₁ · (!a₂) = a₁.
Proof.
  exact (pr12 (pr222 (pr222 (pr222 (pr222 A)))) a₁ a₂).
Defined.

Definition linear_combinatory_algebra_w
           (A : linear_combinatory_algebra)
  : A
  := pr1 (pr222 (pr222 A)).

Notation "'W'" := (linear_combinatory_algebra_w _) : lca.

Proposition linear_combinatory_algebra_w_eq
            {A : linear_combinatory_algebra}
            (a₁ a₂ : A)
  : W · a₁ · (!a₂) = a₁ · (!a₂) · (!a₂).
Proof.
  exact (pr122 (pr222 (pr222 (pr222 (pr222 A)))) a₁ a₂).
Defined.

Definition linear_combinatory_algebra_d
           (A : linear_combinatory_algebra)
  : A
  := pr12 (pr222 (pr222 A)).

Notation "'D'" := (linear_combinatory_algebra_d _) : lca.

Proposition linear_combinatory_algebra_d_eq
            {A : linear_combinatory_algebra}
            (a : A)
  : D · (!a) = a.
Proof.
  exact (pr1 (pr222 (pr222 (pr222 (pr222 (pr222 A))))) a).
Defined.

Definition linear_combinatory_algebra_delta
           (A : linear_combinatory_algebra)
  : A
  := pr122 (pr222 (pr222 A)).

Notation "'δ'" := (linear_combinatory_algebra_delta _) : lca.

Proposition linear_combinatory_algebra_delta_eq
            {A : linear_combinatory_algebra}
            (a : A)
  : δ · (!a) = !(!a).
Proof.
  exact (pr12 (pr222 (pr222 (pr222 (pr222 (pr222 A))))) a).
Defined.

Definition linear_combinatory_algebra_f
           (A : linear_combinatory_algebra)
  : A
  := pr1 (pr222 (pr222 (pr222 A))).

Notation "'F'" := (linear_combinatory_algebra_f _) : lca.

Proposition linear_combinatory_algebra_f_eq
            {A : linear_combinatory_algebra}
            (a₁ a₂ : A)
  : F · (!a₁) · (!a₂) = !(a₁ · a₂).
Proof.
  exact (pr22 (pr222 (pr222 (pr222 (pr222 (pr222 A))))) a₁ a₂).
Defined.

Coercion linear_combinatory_algebra_to_bi_algebra
         (A : linear_combinatory_algebra)
  : bi_algebra.
Proof.
  use (make_bi_algebra A I B).
  - apply linear_combinatory_algebra_i_eq.
  - apply linear_combinatory_algebra_b_eq.
Defined.

(** * 2. Derived combinators *)
Definition linear_combinatory_algebra_s
           (A : linear_combinatory_algebra)
  : A
  := B · (B · W) · (B · B · C).

Notation "'S'" := (linear_combinatory_algebra_s _) : lca.

Proposition linear_combinatory_algebra_s_eq
            {A : linear_combinatory_algebra}
            (a₁ a₂ a₃ : A)
  : S · a₁ · a₂ · (!a₃) = a₁ · (!a₃) · (a₂ · (!a₃)).
Proof.
  unfold linear_combinatory_algebra_s.
  rewrite !linear_combinatory_algebra_b_eq.
  rewrite linear_combinatory_algebra_w_eq.
  rewrite !linear_combinatory_algebra_b_eq.
  rewrite !linear_combinatory_algebra_c_eq.
  apply idpath.
Qed.

Definition linear_combinatory_algebra_ks
           (A : linear_combinatory_algebra)
  : A
  := K · I.

Notation "'K*'" := (linear_combinatory_algebra_ks _) : lca.

Proposition linear_combinatory_algebra_ks_eq
            {A : linear_combinatory_algebra}
            (a₁ a₂ : A)
  : K* · (!a₁) · a₂ = a₂.
Proof.
  unfold linear_combinatory_algebra_ks.
  rewrite linear_combinatory_algebra_k_eq.
  rewrite linear_combinatory_algebra_i_eq.
  apply idpath.
Qed.

(** * 3. The combinatory algebra associated to a linear combinatory algebra *)
Definition lca_to_ca_app
           {A : linear_combinatory_algebra}
           (a₁ a₂ : A)
  : A
  := a₁ · (!a₂).

Arguments lca_to_ca_app /.

Section LinearCombinatoryAlgebraToCombinatory.
  Context (A : linear_combinatory_algebra).

  Definition lca_to_ca_applicative
    : applicative_structure.
  Proof.
    use make_applicative_structure.
    - exact A.
    - exact lca_to_ca_app.
  Defined.

  Definition lca_to_ca
    : combinatory_algebra.
  Proof.
    use make_combinatory_algebra_bckw.
    - exact lca_to_ca_applicative.
    - exact (B · (C · (B · B · B) · (C · (B · (C · F) · δ))) · D).
    - exact (B · C · D).
    - exact (B · K · D).
    - exact (B · W · D).
    - abstract
        (intros a₁ a₂ a₃ ; cbn ;
         rewrite linear_combinatory_algebra_b_eq ;
         rewrite linear_combinatory_algebra_d_eq ;
         rewrite linear_combinatory_algebra_c_eq ;
         rewrite !linear_combinatory_algebra_b_eq ;
         rewrite linear_combinatory_algebra_c_eq ;
         rewrite linear_combinatory_algebra_b_eq ;
         rewrite linear_combinatory_algebra_c_eq ;
         rewrite linear_combinatory_algebra_delta_eq ;
         rewrite linear_combinatory_algebra_f_eq ;
         apply idpath).
    - abstract
        (intros a₁ a₂ a₃ ; cbn ;
         rewrite linear_combinatory_algebra_b_eq ;
         rewrite linear_combinatory_algebra_c_eq ;
         rewrite linear_combinatory_algebra_d_eq ;
         apply idpath).
    - abstract
        (intros a₁ a₂ ; cbn ;
         rewrite linear_combinatory_algebra_b_eq ;
         rewrite linear_combinatory_algebra_k_eq ;
         rewrite linear_combinatory_algebra_d_eq ;
         apply idpath).
    - abstract
        (intros a₁ a₂ ; cbn ;
         rewrite linear_combinatory_algebra_b_eq ;
         rewrite linear_combinatory_algebra_w_eq ;
         rewrite linear_combinatory_algebra_d_eq ;
         apply idpath). 
  Defined.
End LinearCombinatoryAlgebraToCombinatory.
