Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Limits.ProductEquivalences.

Require Import PseudoMonoid.Basics.

Local Open Scope cat.

Definition mor_between_binproducts
           {B : bicat}
           {x y : B}
           (p₁ p₂ : binprod_cone x y)
           (Hp₂ : has_binprod_ump p₂)
  : p₁ --> p₂.
Proof.
  use (binprod_ump_1cell Hp₂).
  - exact (binprod_cone_pr1 p₁).
  - exact (binprod_cone_pr2 p₁).
Defined.

Definition mor_between_binproducts_comp
           {B : bicat}
           {x y : B}
           (p₁ p₂ : binprod_cone x y)
           (Hp₁ : has_binprod_ump p₁)
           (Hp₂ : has_binprod_ump p₂)
  : mor_between_binproducts p₁ p₂ Hp₂ · mor_between_binproducts p₂ p₁ Hp₁
    ==>
    id₁ _.
Proof.
  use (binprod_ump_2cell Hp₁).
  - exact (rassociator _ _ _
           • (_ ◃ binprod_ump_1cell_pr1 _ _ _ _)
           • binprod_ump_1cell_pr1 _ _ _ _
           • linvunitor _).
  - exact (rassociator _ _ _
           • (_ ◃ binprod_ump_1cell_pr2 _ _ _ _)
           • binprod_ump_1cell_pr2 _ _ _ _
           • linvunitor _).
Defined.

Definition mor_between_binproducts_comp_inv
           {B : bicat}
           {x y : B}
           (p₁ p₂ : binprod_cone x y)
           (Hp₁ : has_binprod_ump p₁)
           (Hp₂ : has_binprod_ump p₂)
  : id₁ _
    ==>
    mor_between_binproducts p₁ p₂ Hp₂ · mor_between_binproducts p₂ p₁ Hp₁.
Proof.
  use (binprod_ump_2cell Hp₁).
  - exact (lunitor _
           • (binprod_ump_1cell_pr1 _ _ _ _)^-1
           • (_ ◃ (binprod_ump_1cell_pr1 _ _ _ _)^-1)
           • lassociator _ _ _).
  - exact (lunitor _
           • (binprod_ump_1cell_pr2 _ _ _ _)^-1
           • (_ ◃ (binprod_ump_1cell_pr2 _ _ _ _)^-1)
           • lassociator _ _ _).
Defined.

Proposition mor_between_binproducts_comp_left
           {B : bicat}
           {x y : B}
           (p₁ p₂ : binprod_cone x y)
           (Hp₁ : has_binprod_ump p₁)
           (Hp₂ : has_binprod_ump p₂)
  : mor_between_binproducts_comp p₁ p₂ Hp₁ Hp₂
    • mor_between_binproducts_comp_inv p₁ p₂ Hp₁ Hp₂
    =
    id₂ _.
Proof.
  use (binprod_ump_2cell_unique_alt Hp₁).
  - rewrite id2_rwhisker.
    rewrite <- rwhisker_vcomp.
    unfold mor_between_binproducts_comp, mor_between_binproducts_comp_inv.
    rewrite !binprod_ump_2cell_pr1.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_rinv.
      rewrite id2_left.
      apply idpath.
    }
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
  - rewrite id2_rwhisker.
    rewrite <- rwhisker_vcomp.
    unfold mor_between_binproducts_comp, mor_between_binproducts_comp_inv.
    rewrite !binprod_ump_2cell_pr2.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_rinv.
      rewrite id2_left.
      apply idpath.
    }
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

Proposition mor_between_binproducts_comp_right
           {B : bicat}
           {x y : B}
           (p₁ p₂ : binprod_cone x y)
           (Hp₁ : has_binprod_ump p₁)
           (Hp₂ : has_binprod_ump p₂)
  : mor_between_binproducts_comp_inv p₁ p₂ Hp₁ Hp₂
    • mor_between_binproducts_comp p₁ p₂ Hp₁ Hp₂
    =
    id₂ _.
Proof.
  use (binprod_ump_2cell_unique_alt Hp₁).
  - rewrite id2_rwhisker.
    rewrite <- rwhisker_vcomp.
    unfold mor_between_binproducts_comp, mor_between_binproducts_comp_inv.
    rewrite !binprod_ump_2cell_pr1.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      apply id2_left.
    }
    apply lunitor_linvunitor.
  - rewrite id2_rwhisker.
    rewrite <- rwhisker_vcomp.
    unfold mor_between_binproducts_comp, mor_between_binproducts_comp_inv.
    rewrite !binprod_ump_2cell_pr2.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      apply id2_left.
    }
    apply lunitor_linvunitor.
Qed.

Definition mor_between_binproducts_comp_inv2cell
           {B : bicat}
           {x y : B}
           (p₁ p₂ : binprod_cone x y)
           (Hp₁ : has_binprod_ump p₁)
           (Hp₂ : has_binprod_ump p₂)
  : invertible_2cell
      (mor_between_binproducts p₁ p₂ Hp₂ · mor_between_binproducts p₂ p₁ Hp₁)
      (id₁ _).
Proof.
  use make_invertible_2cell.
  - exact (mor_between_binproducts_comp p₁ p₂ Hp₁ Hp₂).
  - use make_is_invertible_2cell.
    + exact (mor_between_binproducts_comp_inv p₁ p₂ Hp₁ Hp₂).
    + apply mor_between_binproducts_comp_left.
    + apply mor_between_binproducts_comp_right.
Defined.

Definition binproduct_adj_equiv
           {B : bicat}
           {x y : B}
           (p₁ p₂ : binprod_cone x y)
           (Hp₁ : has_binprod_ump p₁)
           (Hp₂ : has_binprod_ump p₂)
  : adjoint_equivalence p₁ p₂.
Proof.
  use equiv_to_adjequiv.
  - exact (mor_between_binproducts p₁ p₂ Hp₂).
  - simple refine (_ ,, _ ,, _).
    + simple refine (_ ,, _ ,, _).
      * exact (mor_between_binproducts p₂ p₁ Hp₁).
      * exact (inv_of_invertible_2cell (mor_between_binproducts_comp_inv2cell p₁ p₂ Hp₁ Hp₂)).
      * exact (mor_between_binproducts_comp_inv2cell p₂ p₁ Hp₂ Hp₁).
    + apply property_from_invertible_2cell.
    + apply property_from_invertible_2cell.
Defined.
           
Definition psfunctor_preserves_final_chosen
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
           (T₁ : bifinal_obj B₁)
           (T₂ : bifinal_obj B₂)
           (H : left_adjoint_equivalence (is_bifinal_1cell_property T₂ (F T₁)))
  : preserves_bifinal F.
Proof.
  intros x Hx.
  use is_bifinal_left_adjoint_equivalence.
  - exact T₂.
  - exact (left_adjoint_right_adjoint H · #F (is_bifinal_1cell_property Hx _)).
  - use comp_left_adjoint_equivalence.
    + apply inv_left_adjoint_equivalence.
    + use psfunctor_preserves_adjequiv'.
      apply bifinal_unique_adj_eqv.
      exact T₁.
  - exact T₂.
Defined.

Definition psfunctor_preserves_binproducts
           {B₁ B₂ : bicat_with_binprod}
           (F : psfunctor B₁ B₂)
           (H : ∏ (x y : B₁),
                left_adjoint_equivalence
                  (⟨ #F (π₁ : x ⊗ y --> x) , #F (π₂ : x ⊗ y --> y) ⟩))
  : preserves_binprods F.
Proof.
  intros x y p Hp.
  use (has_binprod_ump_left_adjoint_equivalence
         π₁ π₂
         (pr2 (binprod_of _ (F x) (F y)))).
  - exact (id₁ _).
  - exact (id₁ _).
  - refine (left_adjoint_right_adjoint (H x y) · #F (binproduct_adj_equiv _ _ _ Hp)).
    exact (pr2 (binprod_of B₁ x y)).
  - apply internal_adjoint_equivalence_identity.
  - apply internal_adjoint_equivalence_identity.
  - use comp_left_adjoint_equivalence.
    + apply inv_left_adjoint_equivalence.
    + use psfunctor_preserves_adjequiv'.
      apply binproduct_adj_equiv.
  - cbn.
    refine (comp_of_invertible_2cell
              _
              (rinvunitor_invertible_2cell _)).
    refine (comp_of_invertible_2cell
              _
              (lunitor_invertible_2cell _)).
    refine (comp_of_invertible_2cell
              _
              (rwhisker_of_invertible_2cell
                 _
                 (left_equivalence_counit_iso (H x y)))).
    refine (comp_of_invertible_2cell
              _
              (lassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell
              (rassociator_invertible_2cell _ _ _)
              _).
    refine (lwhisker_of_invertible_2cell _ _).
    refine (comp_of_invertible_2cell (psfunctor_comp F _ _) _).
    refine (comp_of_invertible_2cell
              _
              (inv_of_invertible_2cell (prod_1cell_pr1 _ _ _))).
    use psfunctor_inv2cell.
    apply binprod_ump_1cell_pr1.
  - cbn.
    refine (comp_of_invertible_2cell
              _
              (rinvunitor_invertible_2cell _)).
    refine (comp_of_invertible_2cell
              _
              (lunitor_invertible_2cell _)).
    refine (comp_of_invertible_2cell
              _
              (rwhisker_of_invertible_2cell
                 _
                 (left_equivalence_counit_iso (H x y)))).
    refine (comp_of_invertible_2cell
              _
              (lassociator_invertible_2cell _ _ _)).
    refine (comp_of_invertible_2cell
              (rassociator_invertible_2cell _ _ _)
              _).
    refine (lwhisker_of_invertible_2cell _ _).
    refine (comp_of_invertible_2cell (psfunctor_comp F _ _) _).
    refine (comp_of_invertible_2cell
              _
              (inv_of_invertible_2cell (prod_1cell_pr2 _ _ _))).
    use psfunctor_inv2cell.
    apply binprod_ump_1cell_pr2.
Defined.
