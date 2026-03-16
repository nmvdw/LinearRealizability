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

Proposition prod_pstrans_id
            {B₁ B₂ : bicat}
            {B₃ : bicat_with_binprod}
            {F G H : psfunctor B₂ B₃}
            (K : psfunctor B₁ B₂)
            (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
            (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K))
            (x : B₁)
  : (_ ◃ (prod_psfunctor_id F G (K x) • ##F (psfunctor_id K x) ⊗₂ ##G (psfunctor_id K x)))
    • prod_psnaturality K τ₁ τ₂ (id₁ x)
    =
    (runitor _ • linvunitor _)
    • ((psfunctor_id H (K x) • ##H (psfunctor_id K x)) ▹ _).
Proof.
  use binprod_ump_2cell_unique_alt.
  - apply (pr2 B₃).
  - rewrite <- !rwhisker_vcomp.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        apply prod_psnaturality_pr1.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        exact (prod_psfunctor_id_pr1 F G (K x)).
      }
      rewrite pair_2cell_pr1.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      apply maponpaths_2.
      apply maponpaths.
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      apply id2_left.
    }
    etrans.
    {
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite lunitor_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      do 4 apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker.
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- vcomp_whisker.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite lwhisker_vcomp.
        exact (pstrans_id τ₁ x).
      }
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_runitor.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite rinvunitor_runitor.
      rewrite id2_left.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite linvunitor_assoc.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        refine (!_).
        apply maponpaths.
        apply rwhisker_vcomp.
      }
      refine (!_).
      apply rwhisker_vcomp.
    }
    rewrite !vassocl.
    apply maponpaths.
    refine (_ @ id2_right _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_left.
    }
    apply rassociator_lassociator.
  - rewrite <- !rwhisker_vcomp.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        apply prod_psnaturality_pr2.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        exact (prod_psfunctor_id_pr2 F G (K x)).
      }
      rewrite pair_2cell_pr2.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      apply maponpaths_2.
      apply maponpaths.
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      apply id2_left.
    }
    etrans.
    {
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite lunitor_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      do 4 apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker.
      rewrite !vassocr.
      rewrite rinvunitor_triangle.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- vcomp_whisker.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite lwhisker_vcomp.
        exact (pstrans_id τ₂ x).
      }
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_runitor.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite rinvunitor_runitor.
      rewrite id2_left.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite linvunitor_assoc.
    rewrite !vassocl.
    apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        refine (!_).
        apply maponpaths.
        apply rwhisker_vcomp.
      }
      refine (!_).
      apply rwhisker_vcomp.
    }
    rewrite !vassocl.
    apply maponpaths.
    refine (_ @ id2_right _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_left.
    }
    apply rassociator_lassociator.
Qed.
