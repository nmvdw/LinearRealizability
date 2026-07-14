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
Require Import UniMath.Bicategories.Objects.CartesianObject.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Limits.ProductEquivalences.

Local Open Scope cat.

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

Definition bicat_with_finprod
  : UU
  := ∑ (B : bicat), bifinal_obj B × has_binprod B.

Coercion bicat_with_finprod_to_bicat
         (B : bicat_with_finprod)
  : bicat
  := pr1 B.
         
Definition bicat_with_finprod_final
           (B : bicat_with_finprod)
  : bifinal_obj B
  := pr12 B.

Definition bicat_with_finprod_binprod
           (B : bicat_with_finprod)
  : has_binprod B
  := pr22 B.

Coercion bicat_with_finprod_to_bicat_with_binprod
         (B : bicat_with_finprod)
  : bicat_with_binprod
  := pr1 B ,, bicat_with_finprod_binprod B.
         
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


Section PreservesBinProdsAdjequiv.
  Context {B₁ B₂ : bicat_with_binprod}
          (F : psfunctor B₁ B₂)
          (HF : preserves_binprods F)
          (x y : B₁).

  Let H : has_binprod_ump (psfunctor_binprod_cone F (pr1 (binprod_of B₁ x y)))
    := HF _ _ _ (pr2 (binprod_of _ x y)).
  
  Definition preserves_binprods_adjequiv_mor
    : F (x ⊗ y) --> F x ⊗ F y
    := ⟨ #F π₁ , #F π₂ ⟩.

  Definition preserves_binprods_adjequiv_inv
    : F x ⊗ F y --> F (x ⊗ y)
    := binprod_ump_1cell H π₁ π₂.

  Definition preserves_binprods_adjequiv_unit
    : id₁ _ ==> preserves_binprods_adjequiv_mor · preserves_binprods_adjequiv_inv.
  Proof.
    use (binprod_ump_2cell H).
    - refine (_ • lassociator _ _ _).
      refine (_ • (_ ◃ (binprod_ump_1cell_pr1 H _ _ _)^-1)).
      refine (_ • (binprod_ump_1cell_pr1 _ _ _ _)^-1).
      apply lunitor.
    - refine (_ • lassociator _ _ _).
      refine (_ • (_ ◃ (binprod_ump_1cell_pr2 H _ _ _)^-1)).
      refine (_ • (binprod_ump_1cell_pr2 _ _ _ _)^-1).
      apply lunitor.
  Defined.

  Definition is_invertible_2cell_preserves_binprods_adjequiv_unit
    : is_invertible_2cell preserves_binprods_adjequiv_unit.
  Proof.
    use (binprod_ump_2cell_invertible H).
    - is_iso.
    - is_iso.
  Defined.

  Definition preserves_binprods_adjequiv_counit
    : preserves_binprods_adjequiv_inv · preserves_binprods_adjequiv_mor ==> id₁ _.
  Proof.
    use binprod_ump_2cell.
    - exact (pr2 (binprod_of B₂ (F x) (F y))).
    - refine (rassociator _ _ _ • _).
      refine ((_ ◃ binprod_ump_1cell_pr1 _ _ _ _) • _).
      refine (binprod_ump_1cell_pr1 H _ _ _ • _).
      exact (linvunitor _).
    - refine (rassociator _ _ _ • _).
      refine ((_ ◃ binprod_ump_1cell_pr2 _ _ _ _) • _).
      refine (binprod_ump_1cell_pr2 H _ _ _ • _).
      exact (linvunitor _).
  Defined.

  Definition is_invertible_2cell_preserves_binprods_adjequiv_counit
    : is_invertible_2cell preserves_binprods_adjequiv_counit.
  Proof.
    use binprod_ump_2cell_invertible.
    - is_iso ; apply property_from_invertible_2cell.
    - is_iso ; apply property_from_invertible_2cell.
  Defined.

  Definition preserves_binprods_adjequiv
    : left_adjoint_equivalence preserves_binprods_adjequiv_mor.
  Proof.
    use equiv_to_adjequiv.
    simple refine (_ ,, _).
    - simple refine (_ ,, _ ,, _).
      + exact preserves_binprods_adjequiv_inv.
      + exact preserves_binprods_adjequiv_unit.
      + exact preserves_binprods_adjequiv_counit.
    - split.
      + exact is_invertible_2cell_preserves_binprods_adjequiv_unit.
      + exact is_invertible_2cell_preserves_binprods_adjequiv_counit.
  Defined.
End PreservesBinProdsAdjequiv.
(*
Section PseudoFunctorPreservesCartesian.
  Context {B₁ B₂ : bicat_with_finprod}
          (F : psfunctor B₁ B₂).

  Let T₁ : bifinal_obj B₁ := bicat_with_finprod_final B₁.
  Let T₂ : bifinal_obj B₂ := bicat_with_finprod_final B₂.
  Let BP₁ : has_binprod B₁ := bicat_with_finprod_binprod B₁.
  Let BP₂ : has_binprod B₂ := bicat_with_finprod_binprod B₂.

  Definition psfunctor_preserves_cartesian_terminal
             (HF : preserves_bifinal F)
             {x : B₁}
             (Hx : cartesian_terminal_via_adj x T₁)
    : cartesian_terminal_via_adj (F x) T₂.
  Proof.
    use left_adjoint_invertible.
    - exact (#F (is_bifinal_1cell_property T₁ x) · is_bifinal_1cell_property T₂ _).
    - use is_bifinal_invertible_2cell_property.
      exact T₂.
    - use comp_left_adjoint.
      + use psfunctor_left_adjoint.
        exact Hx.
      + use bifinal_unique_adj_eqv.
        apply HF.
        exact T₁.
  Defined.
  
  Definition psfunctor_preserves_cartesian_prod_cell
             (HF : preserves_binprods F)
             {x : B₁}
             (Hx : cartesian_prod_via_adj x BP₁)
    : #F ⟨ id₁ _ , id₁ _ ⟩ · preserves_binprods_adjequiv_mor F x x
      ==>
      binprod_ump_1cell (pr2 (BP₂ (F x) (F x))) (id₁ _) (id₁ _).
  Proof.
    use binprod_ump_2cell.
    - exact (pr2 (BP₂ (F x) (F x))).
    - refine (rassociator _ _ _ • _).
      refine ((_ ◃ binprod_ump_1cell_pr1 _ _ _ _) • _).
      refine (psfunctor_comp _ _ _ • _).
      refine (##F (prod_1cell_pr1 _ _ _) • _).
      refine ((psfunctor_id F x)^-1 • _).
      exact ((binprod_ump_1cell_pr1 _ _ _ _)^-1).
    - refine (rassociator _ _ _ • _).
      refine ((_ ◃ binprod_ump_1cell_pr2 _ _ _ _) • _).
      refine (psfunctor_comp _ _ _ • _).
      refine (##F (prod_1cell_pr2 _ _ _) • _).
      refine ((psfunctor_id F x)^-1 • _).
      exact ((binprod_ump_1cell_pr2 _ _ _ _)^-1).
  Defined.      
      
  Definition psfunctor_preserves_cartesian_prod
             (HF : preserves_binprods F)
             {x : B₁}
             (Hx : cartesian_prod_via_adj x BP₁)
    : cartesian_prod_via_adj (F x) BP₂.
  Proof.
    use left_adjoint_invertible.
    - exact (#F ⟨ id₁ _ , id₁ _ ⟩ · preserves_binprods_adjequiv_mor F x x).
    - use make_invertible_2cell.
      + exact (psfunctor_preserves_cartesian_prod_cell HF Hx).
      + use binprod_ump_2cell_invertible ; is_iso.
        * apply property_from_invertible_2cell.
        * apply property_from_invertible_2cell.
        * exact (psfunctor_inv2cell F (prod_1cell_pr1 _ _ _)).
        * apply property_from_invertible_2cell.
        * apply property_from_invertible_2cell.
        * exact (psfunctor_inv2cell F (prod_1cell_pr2 _ _ _)).
    - use comp_left_adjoint.
      + use psfunctor_left_adjoint.
        exact Hx.
      + exact (preserves_binprods_adjequiv F HF x x).
  Defined.

  Definition psfunctor_preserves_cartesian_obj
             (HF₁ : preserves_bifinal F)
             (HF₂ : preserves_binprods F)
             {x : B₁}
             (Hx : cartesian_ob_via_adj x T₁ BP₁)
    : cartesian_ob_via_adj (F x) T₂ BP₂.
  Proof.
    split.
    - exact (psfunctor_preserves_cartesian_terminal HF₁ (pr1 Hx)).
    - exact (psfunctor_preserves_cartesian_prod HF₂ (pr2 Hx)).
  Defined.
End PseudoFunctorPreservesCartesian.
 *)
