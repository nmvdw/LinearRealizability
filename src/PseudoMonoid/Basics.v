Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

Definition bicat_with_finprod
  : UU
  := ∑ (B : bicat), bifinal_obj B × has_binprod B.

Coercion bicat_with_finprod_to_binprod
         (B : bicat_with_finprod)
  : bicat_with_binprod
  := pr1 B ,, pr22 B.

Definition bicat_with_finprod_final
          (B : bicat_with_finprod)
  : bifinal_obj B
  := pr12 B.

Coercion bifinal_obj_to_obj
         {B : bicat}
         (T : bifinal_obj B)
  : B
  := pr1 T.

Coercion bifinal_obj_to_is_bifinal
         {B : bicat}
         (T : bifinal_obj B)
  : is_bifinal T
  := pr2 T.

Definition prod_pair_cell
           {B : bicat_with_binprod}
           {x y₁ y₂ z₁ z₂ : B}
           (f₁ : x --> y₁)
           (f₂ : x --> y₂)
           (g₁ : y₁ --> z₁)
           (g₂ : y₂ --> z₂)
  : ⟨ f₁ , f₂ ⟩ · (g₁ ⊗₁ g₂) ==> ⟨ f₁ · g₁ , f₂ · g₂ ⟩.
Proof.
  use (binprod_ump_2cell (pr2 (binprod_of B z₁ z₂))).
  - exact (rassociator _ _ _
           • (_ ◃ pair_1cell_pr1 _ _ _)
           • lassociator _ _ _
           • (prod_1cell_pr1 _ _ _ ▹ _)
           • inv_of_invertible_2cell (prod_1cell_pr1 _ _ _)).
  - exact (rassociator _ _ _
           • (_ ◃ pair_1cell_pr2 _ _ _)
           • lassociator _ _ _
           • (prod_1cell_pr2 _ _ _ ▹ _)
           • inv_of_invertible_2cell (prod_1cell_pr2 _ _ _)).
Defined.

Proposition prod_pair_cell_pr1
            {B : bicat_with_binprod}
            {x y₁ y₂ z₁ z₂ : B}
            (f₁ : x --> y₁)
            (f₂ : x --> y₂)
            (g₁ : y₁ --> z₁)
            (g₂ : y₂ --> z₂)
  : prod_pair_cell f₁ f₂ g₁ g₂ ▹ π₁
    =
    rassociator _ _ _
    • (_ ◃ pair_1cell_pr1 _ _ _)
    • lassociator _ _ _
    • (prod_1cell_pr1 _ _ _ ▹ _)
    • inv_of_invertible_2cell (prod_1cell_pr1 _ _ _).
Proof.
  apply binprod_ump_2cell_pr1.
Qed.

Proposition prod_pair_cell_pr2
            {B : bicat_with_binprod}
            {x y₁ y₂ z₁ z₂ : B}
            (f₁ : x --> y₁)
            (f₂ : x --> y₂)
            (g₁ : y₁ --> z₁)
            (g₂ : y₂ --> z₂)
  : prod_pair_cell f₁ f₂ g₁ g₂ ▹ π₂
    =
    rassociator _ _ _
    • (_ ◃ pair_1cell_pr2 _ _ _)
    • lassociator _ _ _
    • (prod_1cell_pr2 _ _ _ ▹ _)
    • inv_of_invertible_2cell (prod_1cell_pr2 _ _ _).
Proof.
  apply binprod_ump_2cell_pr2.
Qed.

Definition prod_pair_invertible_2cell
           {B : bicat_with_binprod}
           {x y₁ y₂ z₁ z₂ : B}
           (f₁ : x --> y₁)
           (f₂ : x --> y₂)
           (g₁ : y₁ --> z₁)
           (g₂ : y₂ --> z₂)
  : invertible_2cell (⟨ f₁ , f₂ ⟩ · (g₁ ⊗₁ g₂)) (⟨ f₁ · g₁ , f₂ · g₂ ⟩).
Proof.
  use make_invertible_2cell.
  - exact (prod_pair_cell f₁ f₂ g₁ g₂).
  - use binprod_ump_2cell_invertible.
    + is_iso ; apply property_from_invertible_2cell.
    + is_iso ; apply property_from_invertible_2cell.
Defined.


Definition prod_invertible_2cell
           {B : bicat_with_binprod}
           {a b₁ b₂ : B}
           {f₁ f₂ : a --> b₁}
           {g₁ g₂ : a --> b₂}
           (θ₁ : invertible_2cell f₁ f₂)
           (θ₂ : invertible_2cell g₁ g₂)
  : invertible_2cell ⟨ f₁ , g₁ ⟩ ⟨ f₂ , g₂ ⟩.
Proof.
  use make_invertible_2cell.
  - exact ⟪ θ₁ , θ₂ ⟫.
  - use prod_2cell_is_invertible.
    + apply property_from_invertible_2cell.
    + apply property_from_invertible_2cell.
Defined.

Definition pair_invertible_2cell
           {B : bicat_with_binprod}
           {a₁ a₂ b₁ b₂ : B}
           {f₁ f₂ : a₁ --> b₁}
           {g₁ g₂ : a₂ --> b₂}
           (θ₁ : invertible_2cell f₁ f₂)
           (θ₂ : invertible_2cell g₁ g₂)
  : invertible_2cell (f₁ ⊗₁ g₁) (f₂ ⊗₁ g₂).
Proof.
  use make_invertible_2cell.
  - exact (θ₁ ⊗₂ θ₂).
  - use prod_2cell_is_invertible.
    + is_iso.
      apply property_from_invertible_2cell.
    + is_iso.
      apply property_from_invertible_2cell.
Defined.

Section PseudofunctorAdjunction.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          {x y : B₁}
          (l : x --> y)
          (Hl : left_adjoint l).

  Let r :  y --> x := left_adjoint_right_adjoint Hl.
  Let η : id₁ x ==> l · r := left_adjoint_unit Hl.
  Let ε : r · l ==> id₁ y := left_adjoint_counit Hl.

  Definition psfunctor_left_adjoint_data
    : left_adjoint_data (#F l).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (#F r).
    - exact (psfunctor_id F _ • ##F η • (psfunctor_comp F _ _)^-1).
    - exact (psfunctor_comp F _ _ • ##F ε • (psfunctor_id F _)^-1).
  Defined.

  Proposition psfunctor_left_adjoint_axioms
    : left_adjoint_axioms psfunctor_left_adjoint_data.
  Proof.
    split ; cbn -[psfunctor_id psfunctor_comp].
    - rewrite !vassocl.
      rewrite <- psfunctor_id2.
      refine (_ @ maponpaths (λ z, ##F z) (internal_triangle1 Hl)).
      rewrite !psfunctor_vcomp.
      rewrite psfunctor_linvunitor.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite psfunctor_F_runitor.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn -[psfunctor_comp].
      rewrite !vassocl.
      rewrite <- psfunctor_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite vassocr.
        rewrite <- psfunctor_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        apply id2_right.
      }
      rewrite psfunctor_rwhisker.
      apply idpath.
    - rewrite !vassocl.
      rewrite <- psfunctor_id2.
      refine (_ @ maponpaths (λ z, ##F z) (internal_triangle2 Hl)).
      rewrite !psfunctor_vcomp.
      rewrite psfunctor_rinvunitor.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite psfunctor_F_lunitor.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn -[psfunctor_comp].
      rewrite !vassocl.
      rewrite <- psfunctor_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite vassocr.
        rewrite <- psfunctor_lassociator.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        apply id2_right.
      }
      rewrite psfunctor_lwhisker.
      apply idpath.
  Qed.
  
  Definition psfunctor_left_adjoint
    : left_adjoint (#F l).
  Proof.
    simple refine (_ ,, _).
    - exact psfunctor_left_adjoint_data.
    - exact psfunctor_left_adjoint_axioms.
  Defined.
End PseudofunctorAdjunction.

