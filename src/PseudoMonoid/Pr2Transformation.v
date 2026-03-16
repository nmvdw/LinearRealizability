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

Section ProdPsTrans.
  Context {B₁ B₂ : bicat}
          {B₃ : bicat_with_binprod}
          (F : psfunctor B₁ B₂)
          (G₁ G₂ : psfunctor B₂ B₃).

  Definition pr2_pstrans_data
    : pstrans_data
        (comp_psfunctor (prod_psfunctor G₁ G₂) F)
        (comp_psfunctor G₂ F).
  Proof.
    use make_pstrans_data.
    - exact (λ x, π₂).
    - exact (λ x y f, inv_of_invertible_2cell (pair_1cell_pr2 _ _ _)).
  Defined.

  Proposition pr2_pstrans_data_laws
    : is_pstrans pr2_pstrans_data.
  Proof.
    repeat split.
    - intros x y f g θ ; cbn.
      use vcomp_move_L_pV.
      rewrite !vassocr.
      refine (!_).
      use vcomp_move_L_Vp.
      rewrite pair_2cell_pr2.
      rewrite !vassocl.
      unfold pair_1cell_pr2.
      rewrite vcomp_linv.
      rewrite id2_right.
      apply idpath.
    - intros x.
      cbn.
      rewrite <- rwhisker_vcomp.
      rewrite prod_psfunctor_id_pr2.
      rewrite pair_2cell_pr2.
      refine (!_).
      use vcomp_move_L_Vp.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
      }
      rewrite !vassocr.
      rewrite runitor_rinvunitor.
      rewrite id2_left.
      apply lwhisker_vcomp.
    - intros x y z f g ; cbn.
      refine (!_).
      use vcomp_move_L_Vp.
      rewrite <- rwhisker_vcomp.
      rewrite prod_psfunctor_comp_pr2.
      rewrite pair_2cell_pr2.
      etrans.
      {
        do 5 refine (vassocl _ _ _ @ _).
        do 4 apply maponpaths.
        etrans.
        {
          refine (vassocr _ _ _ @ _) ; apply maponpaths_2.
          do 2 refine (vassocr _ _ _ @ _) ; apply maponpaths_2.
          refine (vassocr _ _ _ @ _) ; do 2 apply maponpaths_2.
          do 5 (refine (vassocr _ _ _ @ _) ; apply maponpaths_2).
          refine (vassocr _ _ _ @ _).
          rewrite lassociator_rassociator.
          apply id2_left.
        }
        do 8 refine (vassocl _ _ _ @ _).
        do 5 apply maponpaths.
        do 3 refine (vassocr _ _ _ @ _).
        rewrite vcomp_linv.
        rewrite id2_left.
        refine (vassocl _ _ _ @ _).
        rewrite vcomp_linv.
        apply id2_right.
      }
      rewrite lwhisker_vcomp.
      do 7 refine (vassocr _ _ _ @ _).
      refine (_ @ id2_left _).
      apply maponpaths_2.
      etrans.
      {
        do 3 apply maponpaths_2.
        do 3 refine (vassocl _ _ _ @ _).
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        rewrite id2_right.
        apply idpath.
      }
      do 3 refine (vassocl _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        do 2 refine (vassocr _ _ _ @ _).
        do 2 apply maponpaths_2.
        refine (vassocl _ _ _ @ _).
        rewrite rassociator_lassociator.
        apply id2_right.
      }
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply lassociator_rassociator.
  Qed.
  
  Definition pr2_pstrans
    : pstrans
        (comp_psfunctor (prod_psfunctor G₁ G₂) F)
        (comp_psfunctor G₂ F).
  Proof.
    use make_pstrans.
    - exact pr2_pstrans_data.
    - exact pr2_pstrans_data_laws.
  Defined.
End ProdPsTrans.
