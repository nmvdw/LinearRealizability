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
Require Import PseudoMonoid.ProdTransformation.Data.

Local Open Scope cat.

Proposition prod_pstrans_naturality
            {B₁ B₂ : bicat}
            {B₃ : bicat_with_binprod}
            {F G H : psfunctor B₂ B₃}
            (K : psfunctor B₁ B₂)
            (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
            (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K))
            {x y : B₁}
            {f g : x --> y}
            (θ : f ==> g)
  : (⟨ τ₁ x , τ₂ x ⟩ ◃ ##F (##K θ) ⊗₂ ##G (##K θ)) • prod_psnaturality K τ₁ τ₂ g
    =
    prod_psnaturality K τ₁ τ₂ f • (##H (##K θ) ▹ ⟨ τ₁ y , τ₂ y ⟩).
Proof.
  cbn -[precomp_prod_1cell_invertible].
  use binprod_ump_2cell_unique_alt.
  - apply (pr2 B₃).
  - rewrite <- !rwhisker_vcomp.
    etrans.
    {
      apply maponpaths.
      apply prod_psnaturality_pr1.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite pair_2cell_pr1.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply prod_psnaturality_pr1.
    }
    rewrite !vassocl.
    apply maponpaths.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      exact (psnaturality_natural τ₁ _ _ _ _ θ).
    }
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    rewrite rwhisker_rwhisker.
    apply idpath.
  - rewrite <- !rwhisker_vcomp.
    etrans.
    {
      apply maponpaths.
      apply prod_psnaturality_pr2.
    }
    etrans.
    {
      cbn.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite pair_2cell_pr2.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      rewrite !vassocr.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply prod_psnaturality_pr2.
    }
    rewrite !vassocl.
    apply maponpaths.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      exact (psnaturality_natural τ₂ _ _ _ _ θ).
    }
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    rewrite rwhisker_rwhisker.
    apply idpath.
Qed.
