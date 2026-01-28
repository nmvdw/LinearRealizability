(**

 BI-algebras

 BI-algebras are applicative structures with only the B combinator and I combinator.

 *)
Require Import UniMath.MoreFoundations.All.

Require Import Basics.CombinatoryAlgebra.

Declare Scope bi.
Local Open Scope bi.
Delimit Scope bi with bi.

Notation "a₁ · a₂" := (applicative_structure_op a₁ a₂) : bi.

Definition bi_algebra
  : UU
  := ∑ (A : applicative_structure)
       (i b : A),
     (∏ (a : A), i · a = a)
     ×
     (∏ (a₁ a₂ a₃ : A), b · a₁ · a₂ · a₃ = a₁ · (a₂ · a₃)).     

Definition make_bi_algebra
           (A : applicative_structure)
           (i b : A)
           (pi : ∏ (a : A), i · a = a)
           (pb : ∏ (a₁ a₂ a₃ : A), b · a₁ · a₂ · a₃ = a₁ · (a₂ · a₃))
  : bi_algebra
  := A ,, i ,, b ,, pi ,, pb.

Coercion bi_algebra_to_applicative_structure
         (A : bi_algebra)
  : applicative_structure
  := pr1 A.

Definition bi_algebra_i
           (A : bi_algebra)
  : A
  := pr12 A.

Notation "'I'" := (bi_algebra_i _) : bi.

Proposition bi_algebra_i_eq
            {A : bi_algebra}
            (a : A)
  : I · a = a.
Proof.
  exact (pr1 (pr222 A) a).
Defined.

Definition bi_algebra_b
           (A : bi_algebra)
  : A
  := pr122 A.

Notation "'B'" := (bi_algebra_b _) : bi.

Proposition bi_algebra_b_eq
            {A : bi_algebra}
            (a₁ a₂ a₃ : A)
  : B · a₁ · a₂ · a₃ = a₁ · (a₂ · a₃).
Proof.
  exact (pr2 (pr222 A) a₁ a₂ a₃).
Defined.

Coercion combinatory_algebra_bi
         (A : combinatory_algebra)
  : bi_algebra.
Proof.
  use make_bi_algebra.
  - exact A.
  - exact I%ca.
  - exact B%ca.
  - intro.
    apply combinatory_algebra_i_eq.
  - intros.
    apply combinatory_algebra_b_eq.
Defined.
