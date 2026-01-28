Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Definition preserves_sym_mon_closed_map
           {V₁ V₂ : sym_mon_closed_cat}
           (F : symmetric_strong_monoidal_functor V₁ V₂)
           (x y : V₁)
  : F(x ⊸ y) --> F x ⊸ F y.
Proof.
  use internal_lam.
  refine (mon_functor_tensor F _ _ · _).
  refine (#F _).
  apply internal_eval.  
Defined.

Definition preserves_sym_mon_closed
           {V₁ V₂ : sym_mon_closed_cat}
           (F : symmetric_strong_monoidal_functor V₁ V₂)
  : UU
  := ∏ (x y : V₁), is_z_isomorphism (preserves_sym_mon_closed_map F x y).


Definition left_adjoint_on_unit
           {V₁ V₂ : monoidal_cat}
           (L : V₁ ⟶ V₂)
           (HL : is_left_adjoint L)
           (HR : fmonoidal_lax V₂ V₁ (right_adjoint HL))
           (R := _ ,, HR : lax_monoidal_functor V₂ V₁)
           (ε := adjcounit HL)
  : L I_{V₁} --> I_{V₂}
  := #L(mon_functor_unit R) · ε I_{V₂}.

Definition left_adjoint_on_tensor
           {V₁ V₂ : monoidal_cat}
           (L : V₁ ⟶ V₂)
           (HL : is_left_adjoint L)
           (HR : fmonoidal_lax V₂ V₁ (right_adjoint HL))
           (R := _ ,, HR : lax_monoidal_functor V₂ V₁)
           (η := adjunit HL)
           (ε := adjcounit HL)
           (x y : V₁)
  : L (x ⊗ y) --> L x ⊗ L y
  := #L(η x #⊗ η y) · #L(mon_functor_tensor R (L x) (L y)) · ε (L x ⊗ L y).
