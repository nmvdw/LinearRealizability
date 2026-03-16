Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import PseudoMonoid.Basics.
Require Import PseudoMonoid.ProdPseudoFunctor.

Local Open Scope cat.

Definition prod_psnaturality
           {B₁ B₂ : bicat}
           {B₃ : bicat_with_binprod}
           {F G H : psfunctor B₂ B₃}
           (K : psfunctor B₁ B₂)
           (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
           (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K))
           {x y : B₁}
           (f : x --> y)
  : invertible_2cell
      (⟨ τ₁ x , τ₂ x ⟩ · (#F (#K f) ⊗₁ #G (#K f)))
      (#H(#K f) · ⟨ τ₁ y , τ₂ y ⟩)
  := comp_of_invertible_2cell
       (comp_of_invertible_2cell
          (prod_pair_invertible_2cell _ _ _ _)
          (prod_invertible_2cell
             (psnaturality_of τ₁ f)
             (psnaturality_of τ₂ f)))
       (inv_of_invertible_2cell (precomp_prod_1cell_invertible _ _ _ _)).

Proposition prod_psnaturality_pr1
            {B₁ B₂ : bicat}
            {B₃ : bicat_with_binprod}
            {F G H : psfunctor B₂ B₃}
            (K : psfunctor B₁ B₂)
            (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
            (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K))
            {x y : B₁}
            (f : x --> y)
  : prod_psnaturality K τ₁ τ₂ f ▹ π₁
    =
    rassociator _ _ _
    • (_ ◃ pair_1cell_pr1 _ _ _)
    • lassociator _ _ _
    • (prod_1cell_pr1 _ _ _ ▹ _)
    • psnaturality_of τ₁ f
    • (_ ◃ (prod_1cell_pr1 _ _ _)^-1)
    • lassociator _ _ _.
Proof.
  cbn.
  etrans.
  {
    rewrite <- !rwhisker_vcomp.
    rewrite prod_pair_cell_pr1.
    rewrite prod_2cell_pr1.
    etrans.
    {
      apply maponpaths.
      apply binprod_ump_2cell_pr1.
    }
    rewrite !vassocl.
    cbn.
    do 4 apply maponpaths.
    rewrite !vassocr.
    rewrite vcomp_linv.
    rewrite id2_left.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite vcomp_linv.
    rewrite id2_left.
    apply idpath.
  }
  rewrite !vassocl.
  apply idpath.
Qed.  

Proposition prod_psnaturality_pr2
            {B₁ B₂ : bicat}
            {B₃ : bicat_with_binprod}
            {F G H : psfunctor B₂ B₃}
            (K : psfunctor B₁ B₂)
            (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
            (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K))
            {x y : B₁}
            (f : x --> y)
  : prod_psnaturality K τ₁ τ₂ f ▹ π₂
    =
    rassociator _ _ _
    • (_ ◃ pair_1cell_pr2 _ _ _)
    • lassociator _ _ _
    • (prod_1cell_pr2 _ _ _ ▹ _)
    • psnaturality_of τ₂ f
    • (_ ◃ (prod_1cell_pr2 _ _ _)^-1)
    • lassociator _ _ _.
Proof.
  cbn.
  etrans.
  {
    rewrite <- !rwhisker_vcomp.
    rewrite prod_pair_cell_pr2.
    rewrite prod_2cell_pr2.
    etrans.
    {
      apply maponpaths.
      apply binprod_ump_2cell_pr2.
    }
    rewrite !vassocl.
    cbn.
    do 4 apply maponpaths.
    rewrite !vassocr.
    rewrite vcomp_linv.
    rewrite id2_left.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite vcomp_linv.
    rewrite id2_left.
    apply idpath.
  }
  rewrite !vassocl.
  apply idpath.
Qed.

#[global] Opaque prod_psnaturality.

Definition prod_pstrans_data
           {B₁ B₂ : bicat}
           {B₃ : bicat_with_binprod}
           {F G H : psfunctor B₂ B₃}
           (K : psfunctor B₁ B₂)
           (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
           (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K))
  : pstrans_data (comp_psfunctor H K) (comp_psfunctor (prod_psfunctor F G) K).
Proof.
  use make_pstrans_data.
  - exact (λ x, ⟨ τ₁ x , τ₂ x ⟩).
  - exact (λ x y f, prod_psnaturality K τ₁ τ₂ f).
Defined.
