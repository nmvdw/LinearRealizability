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

Section Composition.
  Context {B₁ B₂ : bicat}
          {B₃ : bicat_with_binprod}
          {F G H : psfunctor B₂ B₃}
          (K : psfunctor B₁ B₂)
          (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
          (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K)).

  Definition prod_pstrans_comp_lhs
             {x y z : B₁}
             (f : x --> y)
             (g : y --> z)
    : ⟨ τ₁ x , τ₂ x ⟩ · (#F (#K f) ⊗₁ #G (#K f) · (#F (#K g) ⊗₁ #G (#K g)))
      ==>
      #H (#K (f · g)) · ⟨ τ₁ z, τ₂ z ⟩
    := (⟨ τ₁ x , τ₂ x ⟩ ◃ (prod_psfunctor_comp F G (#K f) (#K g)
                           • ## F (psfunctor_comp K f g) ⊗₂ ## G (psfunctor_comp K f g)))
       • prod_psnaturality K τ₁ τ₂ (f · g).

  Definition prod_pstrans_comp_rhs
             {x y z : B₁}
             (f : x --> y)
             (g : y --> z)
    : ⟨ τ₁ x , τ₂ x ⟩ · (#F (#K f) ⊗₁ #G (#K f) · (#F (#K g) ⊗₁ #G (#K g)))
      ==>
      #H (#K (f · g)) · ⟨ τ₁ z, τ₂ z ⟩
    := ((((lassociator _ _ _
       • (prod_psnaturality K τ₁ τ₂ f ▹ _))
       • rassociator _ _ _)
       • (_ ◃ prod_psnaturality K τ₁ τ₂ g))
       • lassociator _ _ _)
       • ((psfunctor_comp H (#K f) (#K g) • ## H (psfunctor_comp K f g)) ▹ _).

  Proposition prod_pstrans_comp_pr1
              {x y z : B₁}
              (f : x --> y)
              (g : y --> z)
    : prod_pstrans_comp_lhs f g ▹ π₁ = prod_pstrans_comp_rhs f g ▹ π₁.
  Proof.
    unfold prod_pstrans_comp_lhs, prod_pstrans_comp_rhs.
    cbn -[psfunctor_comp].
    rewrite <- !rwhisker_vcomp.
    do 4 refine (_ @ vassocr _ _ _).
    etrans.
    {
      apply maponpaths.
      exact (prod_psnaturality_pr1 K τ₁ τ₂ (f · g)).
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_vcomp.
      rewrite <- lwhisker_vcomp.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (prod_psfunctor_comp_pr1 F G).
      }
      etrans.
      {
        apply maponpaths.
        apply pair_2cell_pr1.
      }
      do 6 refine (vassocl _ _ _ @ _).
      do 6 apply maponpaths.
      refine (vassocr _ _ _ @ _).
      rewrite vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      do 5 refine (vassocr _ _ _ @ _).
      rewrite lwhisker_vcomp.
      do 4 refine (vassocl _ _ _ @ _).
      apply maponpaths_2.
      apply maponpaths.
      do 6 (refine (vassocl _ _ _ @ _) ; apply maponpaths).
      refine (vassocl _ _ _ @ _).
      rewrite vcomp_linv.
      rewrite id2_right.
      apply idpath.
    }
    use vcomp_move_L_pM ; [ is_iso | ].
    etrans.
    {
      cbn -[psfunctor_comp].
      rewrite <- !lwhisker_vcomp.
      do 6 refine (vassocr _ _ _ @ _).
      do 5 apply maponpaths_2.
      refine (vassocr _ _ _ @ _).
      rewrite rassociator_rassociator.
      apply idpath.
    }
    do 4 refine (_ @ vassocl _ _ _).
    do 2 (use vcomp_move_R_Mp ; [ is_iso | ]).
    etrans.
    {
      do 4 refine (vassocl _ _ _ @ _).
      do 2 apply maponpaths.
      do 4 (refine (vassocl _ _ _ @ _) ; apply maponpaths).
      do 2 refine (vassocr _ _ _ @ _).
      rewrite !lwhisker_vcomp.
      rewrite lwhisker_lwhisker.
      do 2 refine (vassocl _ _ _ @ _).
      apply maponpaths.
      refine (vassocr _ _ _ @ _).
      rewrite <- vcomp_whisker.
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      exact (pstrans_comp τ₁ f g).
    }
    do 8 refine (vassocr _ _ _ @ _).
    refine (!_).
    etrans.
    {
      cbn -[psfunctor_comp].
      do 6 refine (vassocl _ _ _ @ _).
      do 4 apply maponpaths.
      do 2 refine (vassocr _ _ _ @ _).
      rewrite !rwhisker_vcomp.
      rewrite rwhisker_rwhisker_alt.
      refine (vassocl _ _ _ @ _).
      rewrite vcomp_whisker.
      apply idpath.
    }
    do 5 refine (vassocr _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      do 4 refine (vassocl _ _ _ @ _).
      do 3 apply maponpaths.
      rewrite rwhisker_hcomp.
      rewrite !vassocr.
      rewrite inverse_pentagon_2.
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      refine (vassocl _ _ _ @ _).
      rewrite <- lwhisker_lwhisker.
      apply idpath.
    }
    do 5 refine (vassocr _ _ _ @ _).
    refine (_ @ vassocl _ _ _).
    apply maponpaths_2.
    etrans.
    {
      do 4 refine (vassocl _ _ _ @ _).
      do 2 apply maponpaths.
      do 2 refine (vassocr _ _ _ @ _).
      rewrite <- rwhisker_lwhisker_rassociator.
      do 2 refine (vassocl _ _ _ @ _).
      rewrite !lwhisker_vcomp.
      do 2 apply maponpaths.
      apply maponpaths_2.
      exact (prod_psnaturality_pr1 K τ₁ τ₂ g).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        do 5 refine (vassocl _ _ _ @ _).
        apply vassocl.
      }
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply lwhisker_vcomp.
      }
      do 2 refine (vassocr _ _ _ @ _).
      rewrite rassociator_rassociator.
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply lwhisker_vcomp.
      }
      refine (vassocr _ _ _ @ _).
      rewrite lwhisker_lwhisker_rassociator.
      apply idpath.
    }
    etrans.
    {
      do 2 refine (vassocr _ _ _ @ _).
      rewrite rwhisker_rwhisker_alt.
      apply idpath.
    }
    do 2 refine (vassocl _ _ _ @ _).
    do 7 refine (_ @ vassocr _ _ _).
    apply maponpaths.
    etrans.
    {
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      refine (vassocr _ _ _ @ _).
      rewrite vcomp_whisker.
      apply vassocl.
    }
    refine (!_).
    etrans.
    {
      do 7 refine (vassocr _ _ _ @ _).
      rewrite lwhisker_lwhisker_rassociator.
      do 7 refine (vassocl _ _ _ @ _).
      apply idpath.
    }
    refine (_ @ vassocr _ _ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      do 6 apply maponpaths.
      refine (vassocr _ _ _ @ _).
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    etrans.
    {
      do 4 apply maponpaths.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      apply id2_right.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply vassocr.
      }
      refine (!_).
      apply lwhisker_vcomp.
    }
    refine (vassocr _ _ _ @ _).
    do 6 refine (_ @ vassocl _ _ _).
    apply maponpaths_2.
    refine (vassocl _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_hcomp.
      rewrite inverse_pentagon_4.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite rwhisker_lwhisker_rassociator.
    do 3 refine (vassocr _ _ _ @ _).
    refine (_ @ vassocl _ _ _).
    apply maponpaths_2.
    do 2 refine (vassocl _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      exact (prod_psnaturality_pr1 K τ₁ τ₂ f).
    }
    do 5 refine (_ @ vassocr _ _ _).
    use vcomp_move_L_pM ; [ is_iso | ].
    cbn -[psfunctor_comp].
    etrans.
    {
      do 3 refine (vassocr _ _ _ @ _).
      do 2 apply maponpaths_2.
      rewrite <- lassociator_lassociator.
      do 2 refine (vassocl _ _ _ @ _).
      do 2 apply maponpaths.
      refine (rwhisker_vcomp _ _ _ @ _).
      apply maponpaths.
      do 5 (refine (vassocr _ _ _ @ _) ; apply maponpaths_2).
      refine (vassocr _ _ _ @ _).
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    do 2 refine (vassocl _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      refine (vassocr _ _ _ @ _) ; do 2 apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths.
        do 4 refine (vassocl _ _ _ @ _).
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply rwhisker_vcomp.
      }
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      refine (!_).
      apply rwhisker_lwhisker.
    }
    do 3 refine (vassocl _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      do 4 (refine (vassocl _ _ _ @ _) ; apply maponpaths).
      refine (vassocr _ _ _ @ _).
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    rewrite lwhisker_vcomp.
    rewrite vcomp_linv.
    rewrite lwhisker_id2.
    rewrite id2_right.
    rewrite <- !rwhisker_vcomp.
    do 2 refine (vassocr _ _ _ @ _).
    do 3 refine (_ @ vassocl _ _ _).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      refine (vassocl _ _ _ @ _).
      rewrite <- rwhisker_rwhisker.
      apply vassocr.
    }
    apply maponpaths_2.
    refine (vassocl _ _ _ @ _).
    rewrite <- lassociator_lassociator.
    refine (vassocr _ _ _ @ _).
    apply maponpaths_2.
    refine (vassocr _ _ _ @ _).
    rewrite !lwhisker_vcomp.
    rewrite rassociator_lassociator.
    rewrite lwhisker_id2.
    apply id2_left.
  Qed.

  Proposition prod_pstrans_comp_pr2
              {x y z : B₁}
              (f : x --> y)
              (g : y --> z)
    : prod_pstrans_comp_lhs f g ▹ π₂ = prod_pstrans_comp_rhs f g ▹ π₂.
  Proof.
    unfold prod_pstrans_comp_lhs, prod_pstrans_comp_rhs.
    cbn -[psfunctor_comp].
    rewrite <- !rwhisker_vcomp.
    do 4 refine (_ @ vassocr _ _ _).
    etrans.
    {
      apply maponpaths.
      exact (prod_psnaturality_pr2 K τ₁ τ₂ (f · g)).
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_vcomp.
      rewrite <- lwhisker_vcomp.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (prod_psfunctor_comp_pr2 F G).
      }
      etrans.
      {
        apply maponpaths.
        apply pair_2cell_pr2.
      }
      do 6 refine (vassocl _ _ _ @ _).
      do 6 apply maponpaths.
      refine (vassocr _ _ _ @ _).
      rewrite vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      do 5 refine (vassocr _ _ _ @ _).
      rewrite lwhisker_vcomp.
      do 4 refine (vassocl _ _ _ @ _).
      apply maponpaths_2.
      apply maponpaths.
      do 6 (refine (vassocl _ _ _ @ _) ; apply maponpaths).
      refine (vassocl _ _ _ @ _).
      rewrite vcomp_linv.
      rewrite id2_right.
      apply idpath.
    }
    use vcomp_move_L_pM ; [ is_iso | ].
    etrans.
    {
      cbn -[psfunctor_comp].
      rewrite <- !lwhisker_vcomp.
      do 6 refine (vassocr _ _ _ @ _).
      do 5 apply maponpaths_2.
      refine (vassocr _ _ _ @ _).
      rewrite rassociator_rassociator.
      apply idpath.
    }
    do 4 refine (_ @ vassocl _ _ _).
    do 2 (use vcomp_move_R_Mp ; [ is_iso | ]).
    etrans.
    {
      do 4 refine (vassocl _ _ _ @ _).
      do 2 apply maponpaths.
      do 4 (refine (vassocl _ _ _ @ _) ; apply maponpaths).
      do 2 refine (vassocr _ _ _ @ _).
      rewrite !lwhisker_vcomp.
      rewrite lwhisker_lwhisker.
      do 2 refine (vassocl _ _ _ @ _).
      apply maponpaths.
      refine (vassocr _ _ _ @ _).
      rewrite <- vcomp_whisker.
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      exact (pstrans_comp τ₂ f g).
    }
    do 8 refine (vassocr _ _ _ @ _).
    refine (!_).
    etrans.
    {
      cbn -[psfunctor_comp].
      do 6 refine (vassocl _ _ _ @ _).
      do 4 apply maponpaths.
      do 2 refine (vassocr _ _ _ @ _).
      rewrite !rwhisker_vcomp.
      rewrite rwhisker_rwhisker_alt.
      refine (vassocl _ _ _ @ _).
      rewrite vcomp_whisker.
      apply idpath.
    }
    do 5 refine (vassocr _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      do 4 refine (vassocl _ _ _ @ _).
      do 3 apply maponpaths.
      rewrite rwhisker_hcomp.
      rewrite !vassocr.
      rewrite inverse_pentagon_2.
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      refine (vassocl _ _ _ @ _).
      rewrite <- lwhisker_lwhisker.
      apply idpath.
    }
    do 5 refine (vassocr _ _ _ @ _).
    refine (_ @ vassocl _ _ _).
    apply maponpaths_2.
    etrans.
    {
      do 4 refine (vassocl _ _ _ @ _).
      do 2 apply maponpaths.
      do 2 refine (vassocr _ _ _ @ _).
      rewrite <- rwhisker_lwhisker_rassociator.
      do 2 refine (vassocl _ _ _ @ _).
      rewrite !lwhisker_vcomp.
      do 2 apply maponpaths.
      apply maponpaths_2.
      exact (prod_psnaturality_pr2 K τ₁ τ₂ g).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        do 5 refine (vassocl _ _ _ @ _).
        apply vassocl.
      }
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply lwhisker_vcomp.
      }
      do 2 refine (vassocr _ _ _ @ _).
      rewrite rassociator_rassociator.
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply lwhisker_vcomp.
      }
      refine (vassocr _ _ _ @ _).
      rewrite lwhisker_lwhisker_rassociator.
      apply idpath.
    }
    etrans.
    {
      do 2 refine (vassocr _ _ _ @ _).
      rewrite rwhisker_rwhisker_alt.
      apply idpath.
    }
    do 2 refine (vassocl _ _ _ @ _).
    do 7 refine (_ @ vassocr _ _ _).
    apply maponpaths.
    etrans.
    {
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      refine (vassocr _ _ _ @ _).
      rewrite vcomp_whisker.
      apply vassocl.
    }
    refine (!_).
    etrans.
    {
      do 7 refine (vassocr _ _ _ @ _).
      rewrite lwhisker_lwhisker_rassociator.
      do 7 refine (vassocl _ _ _ @ _).
      apply idpath.
    }
    refine (_ @ vassocr _ _ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      do 6 apply maponpaths.
      refine (vassocr _ _ _ @ _).
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    etrans.
    {
      do 4 apply maponpaths.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      apply id2_right.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply vassocr.
      }
      refine (!_).
      apply lwhisker_vcomp.
    }
    refine (vassocr _ _ _ @ _).
    do 6 refine (_ @ vassocl _ _ _).
    apply maponpaths_2.
    refine (vassocl _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_hcomp.
      rewrite inverse_pentagon_4.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite rwhisker_lwhisker_rassociator.
    do 3 refine (vassocr _ _ _ @ _).
    refine (_ @ vassocl _ _ _).
    apply maponpaths_2.
    do 2 refine (vassocl _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      exact (prod_psnaturality_pr2 K τ₁ τ₂ f).
    }
    do 5 refine (_ @ vassocr _ _ _).
    use vcomp_move_L_pM ; [ is_iso | ].
    cbn -[psfunctor_comp].
    etrans.
    {
      do 3 refine (vassocr _ _ _ @ _).
      do 2 apply maponpaths_2.
      rewrite <- lassociator_lassociator.
      do 2 refine (vassocl _ _ _ @ _).
      do 2 apply maponpaths.
      refine (rwhisker_vcomp _ _ _ @ _).
      apply maponpaths.
      do 5 (refine (vassocr _ _ _ @ _) ; apply maponpaths_2).
      refine (vassocr _ _ _ @ _).
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    do 2 refine (vassocl _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      refine (vassocr _ _ _ @ _) ; do 2 apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths.
        do 4 refine (vassocl _ _ _ @ _).
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply rwhisker_vcomp.
      }
      refine (vassocr _ _ _ @ _).
      apply maponpaths_2.
      refine (!_).
      apply rwhisker_lwhisker.
    }
    do 3 refine (vassocl _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      do 4 (refine (vassocl _ _ _ @ _) ; apply maponpaths).
      refine (vassocr _ _ _ @ _).
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    rewrite lwhisker_vcomp.
    rewrite vcomp_linv.
    rewrite lwhisker_id2.
    rewrite id2_right.
    rewrite <- !rwhisker_vcomp.
    do 2 refine (vassocr _ _ _ @ _).
    do 3 refine (_ @ vassocl _ _ _).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      refine (vassocl _ _ _ @ _).
      rewrite <- rwhisker_rwhisker.
      apply vassocr.
    }
    apply maponpaths_2.
    refine (vassocl _ _ _ @ _).
    rewrite <- lassociator_lassociator.
    refine (vassocr _ _ _ @ _).
    apply maponpaths_2.
    refine (vassocr _ _ _ @ _).
    rewrite !lwhisker_vcomp.
    rewrite rassociator_lassociator.
    rewrite lwhisker_id2.
    apply id2_left.
  Qed.

  Proposition prod_pstrans_comp
              {x y z : B₁}
              (f : x --> y)
              (g : y --> z)
    : prod_pstrans_comp_lhs f g = prod_pstrans_comp_rhs f g.
  Proof.
    use binprod_ump_2cell_unique_alt.
    - apply (pr2 B₃).
    - apply prod_pstrans_comp_pr1.
    - apply prod_pstrans_comp_pr2.
  Qed.
End Composition.
