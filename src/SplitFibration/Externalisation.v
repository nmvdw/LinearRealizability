Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Strictness.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Preservation.Preservation.

Require Import PseudoFunctorPreservation.
Require Import SplitFibration.SplitDispSetCat.
Require Import SplitFibration.TwoCatSplitDispSetCat.
Require Import SplitFibration.TerminalSplitFib.
Require Import SplitFibration.BinProductSplitFib.
Require Import SplitFibration.BicatSplitDispSetCat.
Require Import InternalCategories.InternalCat.
Require Import InternalCategories.InternalFunctor.
Require Import InternalCategories.InternalNatTrans.
Require Import InternalCategories.CatOfInternalCat.
Require Import InternalCategories.TwoCatOfInternalCat.
Require Import InternalCategories.TerminalInternalCat.
Require Import InternalCategories.ProdInternalCat.
Require Import InternalCategories.BicatOfInternalCat.
Require Import PseudoMonoid.Basics.

Local Open Scope cat.

Section Externalisation.
  Context {C : category}
          (PB : Pullbacks C).

  Definition externalisation_internal_cat
             (d : internal_cat PB)
    : split_disp_setcat C.
  Proof.
    use make_split_disp_setcat.
    - exact (internal_cat_disp_cat d).
    - exact (internal_cat_to_cleaving d).
    - exact (is_split_internal_cat_to_cleaving d).
  Defined.

  Definition externalisation_internal_functor
             {d₁ d₂ : internal_cat PB}
             (f : internal_functor d₁ d₂)
    : split_disp_functor
        (externalisation_internal_cat d₁)
        (externalisation_internal_cat d₂).
  Proof.
    use make_split_disp_functor.
    - exact (internal_functor_to_disp_functor f).
    - exact (preserves_cleaving_internal_functor_to_disp_functor f).
  Defined.
  
  Definition externalisation_identitor
             (d : internal_cat PB)
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_identity (internal_cat_disp_cat d))
        (externalisation_internal_functor (identity_internal_functor d)).
  Proof.
    simple refine (_ ,, _).
    - intros x xx ; cbn.
      use eq_to_internal_morphism.
      exact (!(id_right _)).
    - abstract
        (intros x y f xx yy ff ; cbn ;
         use internal_morphism_over_eq ;
         refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
         rewrite eq_to_internal_morphism_left_over, eq_to_internal_morphism_right_over ;
         cbn ;
         rewrite id_right ;
         apply idpath).
  Defined.

  Definition externalisation_compositor
             {d₁ d₂ d₃ : internal_cat PB}
             (f : internal_functor d₁ d₂)
             (g : internal_functor d₂ d₃)
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_composite
           (externalisation_internal_functor f)
           (externalisation_internal_functor g))
        (externalisation_internal_functor (comp_internal_functor f g)).
  Proof.
    simple refine (_ ,, _).
    - intros x xx ; cbn.
      use eq_to_internal_morphism.
      apply assoc'.
    - abstract
        (intros x y h xx yy hh ; cbn ;
         use internal_morphism_over_eq ;
         refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
         rewrite eq_to_internal_morphism_left_over, eq_to_internal_morphism_right_over ;
         cbn ;
         rewrite assoc ;
         apply idpath).
  Defined.

  Definition externalisation_psfunctor_data
    : psfunctor_data
        (strict_bicat_of_internal_cat PB)
        (strict_bicat_of_split_disp_setcat C).
  Proof.
    use make_psfunctor_data.
    - exact (λ d, externalisation_internal_cat d).
    - exact (λ d₁ d₂ f, externalisation_internal_functor f).
    - exact (λ d₁ d₂ f₁ f₂ θ, internal_nat_trans_to_disp_nat_trans θ).
    - exact (λ d, externalisation_identitor d).
    - exact (λ d₁ d₂ d₃ f g, externalisation_compositor f g).
  Defined.

  Proposition externalisation_laws
    : psfunctor_laws externalisation_psfunctor_data.
  Proof.
    repeat split.
    - intros d₁ d₂ f.
      use disp_nat_trans_eq.
      intros x xx.
      use internal_morphism_eq ; cbn.
      rewrite assoc'.
      apply idpath.
    - intros d₁ d₂ f₁ f₂ f₃ θ₁ θ₂.
      use disp_nat_trans_eq.
      intros x xx.
      use internal_morphism_eq ; cbn.
      refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ; cbn.
      rewrite !assoc.
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite id_left.
        apply idpath.
    - intros d₁ d₂ f.
      use disp_nat_trans_eq.
      intros x xx.
      use internal_morphism_eq ; cbn.
      refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
      etrans.
      {
        apply maponpaths.
        exact (idto2mor_two_cat_category_of_split_disp_setcat
                 _ _ _
                 (id_left (externalisation_internal_functor f))
                 xx).
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (internal_cat_idto2mor_disp
                 (id_left (C := cat_of_internal_cat PB) f)
                 xx).
      }
      rewrite eq_to_internal_morphism_right_over.
      refine (transportf_internal_morphism_mor_eq _ _ _ _ @ _).
      rewrite eq_to_internal_morphism_right_over.
      cbn.
      rewrite !assoc'.
      rewrite internal_functor_id'.
      apply idpath.
    - intros d₁ d₂ f.
      use disp_nat_trans_eq.
      intros x xx.
      use internal_morphism_eq ; cbn.
      refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
      etrans.
      {
        apply maponpaths.
        exact (idto2mor_two_cat_category_of_split_disp_setcat
                 _ _ _
                 (id_right (externalisation_internal_functor f))
                 xx).
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (internal_cat_idto2mor_disp
                 (id_right (C := cat_of_internal_cat PB) f)
                 xx).
      }
      rewrite eq_to_internal_morphism_right_over.
      refine (transportf_internal_morphism_mor_eq _ _ _ _ @ _).
      rewrite eq_to_internal_morphism_right_over.
      cbn.
      apply idpath.
    - intros d₁ d₂ d₃ d₄ f₁ f₂ f₃.
      use disp_nat_trans_eq.
      intros x xx.
      use internal_morphism_eq ; cbn.
      refine (transportf_internal_morphism_mor_eq _ _ _ _ @ _).
      refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          exact (idto2mor_two_cat_category_of_split_disp_setcat
                   _ _ _
                   (assoc
                      (externalisation_internal_functor f₁)
                      (externalisation_internal_functor f₂)
                      (externalisation_internal_functor f₃))
                   xx).
        }
        cbn.
        apply idpath.
      }
      rewrite eq_to_internal_morphism_right_over.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (internal_cat_idto2mor_disp (assoc (C := cat_of_internal_cat PB) _ _ _) _).
      }
      rewrite eq_to_internal_morphism_right_over.
      refine (transportf_internal_morphism_mor_eq _ _ _ _ @ _).
      refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
      rewrite internal_functor_eq_to_internal_morphism_over.
      rewrite !eq_to_internal_morphism_right_over.
      cbn.
      apply idpath.
    - intros d₁ d₂ d₃ f g₁ g₂ θ.
      use disp_nat_trans_eq.
      intros x xx.
      use internal_morphism_eq ; cbn.
      refine (transportf_internal_morphism_mor_eq _ _ _ _ @ _).
      refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
      rewrite eq_to_internal_morphism_left_over, eq_to_internal_morphism_right_over.
      cbn.
      rewrite assoc'.
      apply idpath.
    - intros d₁ d₂ d₃ f₁ f₂ g θ.
      use disp_nat_trans_eq.
      intros x xx.
      use internal_morphism_eq ; cbn.
      refine (transportf_internal_morphism_mor_eq _ _ _ _ @ _).
      refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
      rewrite eq_to_internal_morphism_left_over, eq_to_internal_morphism_right_over.
      cbn.
      rewrite assoc'.
      apply idpath.
  Qed.

  Proposition externalisation_invertible_2cells
    : invertible_cells externalisation_psfunctor_data.
  Proof.
    split.
    - intro d.
      use is_invertible_2cell_split_disp_set_cat ; cbn.
      intros Γ x.
      simple refine (_ ,, _ ,, _).
      + use eq_to_internal_morphism.
        exact (id_right _).
      + abstract
          (cbn ;
           use internal_morphism_over_eq ;
           refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
           rewrite eq_to_internal_morphism_right_over ;
           cbn ;
           rewrite id_right ;
           apply idpath).
      + abstract
          (cbn ;
           use internal_morphism_over_eq ;
           refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
           rewrite eq_to_internal_morphism_right_over ;
           cbn ;
           apply idpath).
    - intros d₁ d₂ d₃ f₁ f₂.
      use is_invertible_2cell_split_disp_set_cat ; cbn.
      intros Γ x.
      simple refine (_ ,, _ ,, _).
      + use eq_to_internal_morphism.
        exact (assoc _ _ _).
      + abstract
          (cbn ;
           use internal_morphism_over_eq ;
           refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
           rewrite eq_to_internal_morphism_right_over ;
           cbn ;
           apply idpath).
      + abstract
          (cbn ;
           use internal_morphism_over_eq ;
           refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
           rewrite eq_to_internal_morphism_right_over ;
           cbn ;
           apply idpath).
  Defined.
      
  Definition externalisation_psfunctor
    : psfunctor
        (strict_bicat_of_internal_cat PB)
        (strict_bicat_of_split_disp_setcat C).
  Proof.
    use make_psfunctor.
    - exact externalisation_psfunctor_data.
    - exact externalisation_laws.
    - exact externalisation_invertible_2cells.
  Defined.

  Section PreservationTerminal.
    Context (T : Terminal C).

    Definition externalisation_terminal_disp_functor_data
      : disp_functor_data
          (functor_identity _)
          (terminal_split_disp_setcat C)
          (externalisation_internal_cat (terminal_internal_cat T PB)).
    Proof.
      simple refine (_ ,, _).
      - exact (λ _ _, TerminalArrow _ _).
      - refine (λ x y _ _ f _, _) ; cbn.
        use make_internal_morphism_over.
        + apply TerminalArrow.
        + apply TerminalArrowEq.
        + apply TerminalArrowEq.
    Defined.
    
    Definition externalisation_terminal_disp_functor
      : disp_functor
          (functor_identity _)
          (terminal_split_disp_setcat C)
          (externalisation_internal_cat (terminal_internal_cat T PB)).
    Proof.
      simple refine (_ ,, _).
      - exact externalisation_terminal_disp_functor_data.
      - abstract
          (split ;
           intros ;
           use internal_morphism_over_eq ;
           apply TerminalArrowEq).
    Defined.

    Proposition externalisation_terminal_preserves_cleaving
      : preserves_cleaving
          (cleaving_terminal_disp_cat C)
          (internal_cat_to_cleaving (terminal_internal_cat T PB))
          externalisation_terminal_disp_functor.
    Proof.
      intro ; intros.
      simple refine (_ ,, _).
      - apply TerminalArrowEq.
      - use internal_morphism_over_eq.
        apply TerminalArrowEq.
    Qed.
    
    Definition externalisation_terminal_split_disp_functor
      : split_disp_functor
          (terminal_split_disp_setcat C)
          (externalisation_internal_cat (terminal_internal_cat T PB)).
    Proof.
      use make_split_disp_functor.
      - exact externalisation_terminal_disp_functor.
      - exact externalisation_terminal_preserves_cleaving.
    Defined.

    Definition externalisation_terminal_unit
      : disp_nat_trans
          (nat_trans_id _)
          (disp_functor_identity _)
          (disp_functor_composite
             (disp_functor_to_terminal_disp_cat
                (internal_cat_disp_cat (terminal_internal_cat T PB)))
             externalisation_terminal_disp_functor).
    Proof.
      simple refine (_ ,, _).
      - refine (λ x xx, eq_to_internal_morphism _).
        apply TerminalArrowEq.
      - abstract
          (intro ; intros ;
           use internal_morphism_over_eq ;
           apply TerminalArrowEq).
    Defined.

    Definition externalisation_terminal_counit
      : disp_nat_trans
          (nat_trans_id _)
          (disp_functor_composite
             externalisation_terminal_disp_functor
             (disp_functor_to_terminal_disp_cat
                (internal_cat_disp_cat (terminal_internal_cat T PB))))
          (disp_functor_identity _).
    Proof.
      simple refine (_ ,, _).
      - exact (λ _ _, tt).
      - abstract
          (intro ; intros ;
           apply isapropunit).
    Defined.

    Definition preserves_bifinal_externalisation                 
      : preserves_bifinal externalisation_psfunctor.
    Proof.
      use psfunctor_preserves_final_chosen.
      - exact (bifinal_bicat_of_internal_cat T PB).
      - exact (bifinal_bicat_of_split_disp_setcat C).
      - use equiv_to_adjequiv.
        simple refine (_ ,, _).
        + simple refine (_ ,, _ ,, _).
          * exact externalisation_terminal_split_disp_functor.
          * exact externalisation_terminal_unit.
          * exact externalisation_terminal_counit.
        + split.
          * use is_invertible_2cell_split_disp_set_cat.
            intros x xx ; cbn.
            simple refine (eq_to_internal_morphism _ ,, _ ,, _).
            ** apply TerminalArrowEq.
            ** abstract
                (use internal_morphism_over_eq ;
                 apply TerminalArrowEq).
            ** abstract
                (use internal_morphism_over_eq ;
                 apply TerminalArrowEq).
          * use is_invertible_2cell_split_disp_set_cat.
            intros x xx.
            refine (tt ,, _ ,, _) ; apply isapropunit.
    Defined.
  End PreservationTerminal.

  Section PreservationBinProducts.
    Context (BP : BinProducts C).

    Definition externalisation_binprod_disp_functor_data
               (d₁ d₂ : internal_cat PB)
      : disp_functor_data
          (functor_identity C)
          (prod_split_disp_setcat
             (externalisation_internal_cat d₁)
             (externalisation_internal_cat d₂))
          (externalisation_internal_cat
             (binprod_internal_cat BP d₁ d₂)).
    Proof.
      simple refine (_ ,, _).
      - exact (λ Γ fg, BinProductArrow _ _ (pr1 fg) (pr2 fg)).
      - refine (λ Γ₁ Γ₂ xy₁ xy₂ s fg, _) ; cbn in *.
        use make_internal_morphism_over.
        + exact (BinProductArrow _ _ (pr1 fg) (pr2 fg)).
        + abstract
            (cbn ; unfold binprod_internal_cat_dom ;
             refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _) ;
             rewrite !internal_morphism_over_dom ;
             apply idpath).
        + abstract
            (cbn ; unfold binprod_internal_cat_cod ;
             refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _) ;
             rewrite !internal_morphism_over_cod ;
             exact (!(precompWithBinProductArrow _ _ _ _ _))).
    Defined.

    Proposition externalisation_binprod_disp_functor_laws
                (d₁ d₂ : internal_cat PB)
      : disp_functor_axioms
          (externalisation_binprod_disp_functor_data d₁ d₂).
    Proof.
      split.
      - intros.
        use internal_morphism_over_eq ; cbn.
        unfold binprod_internal_cat_id.
        refine (_ @ !(postcompWithBinProductArrow _ _ _ _ _ _ _)).
        apply idpath.
      - intros.
        use internal_morphism_over_eq.
        unfold transportb.
        refine (!_).
        etrans.
        {
          apply transportf_internal_morphism_mor_eq.
        }
        cbn.
        unfold binprod_internal_cat_comp.
        use BinProductArrowsEq.
        + rewrite !assoc'.
          rewrite !BinProductPr1Commutes.
          etrans.
          {
            apply maponpaths.
            apply BinProductPr1Commutes.
          }
          rewrite !assoc.
          apply maponpaths_2.
          use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
          * rewrite !assoc'.
            rewrite PullbackArrow_PullbackPr1.
            rewrite assoc.
            rewrite PullbackArrow_PullbackPr1.
            rewrite BinProductPr1Commutes.
            apply idpath.
          * rewrite !assoc'.
            rewrite PullbackArrow_PullbackPr2.
            rewrite assoc.
            rewrite PullbackArrow_PullbackPr2.
            rewrite assoc'.
            apply maponpaths.
            apply BinProductPr1Commutes.
        + rewrite !assoc'.
          rewrite !BinProductPr2Commutes.
          etrans.
          {
            apply maponpaths.
            apply BinProductPr2Commutes.
          }
          rewrite !assoc.
          apply maponpaths_2.
          use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
          * rewrite !assoc'.
            rewrite PullbackArrow_PullbackPr1.
            rewrite assoc.
            rewrite PullbackArrow_PullbackPr1.
            rewrite BinProductPr2Commutes.
            apply idpath.
          * rewrite !assoc'.
            rewrite PullbackArrow_PullbackPr2.
            rewrite assoc.
            rewrite PullbackArrow_PullbackPr2.
            rewrite assoc'.
            apply maponpaths.
            apply BinProductPr2Commutes.
    Qed.
        
    Definition externalisation_binprod_disp_functor
               (d₁ d₂ : internal_cat PB)
      : disp_functor
          (functor_identity C)
          (prod_split_disp_setcat
             (externalisation_internal_cat d₁)
             (externalisation_internal_cat d₂))
          (externalisation_internal_cat
             (binprod_internal_cat BP d₁ d₂)).
    Proof.
      simple refine (_ ,, _).
      - exact (externalisation_binprod_disp_functor_data d₁ d₂).
      - exact (externalisation_binprod_disp_functor_laws d₁ d₂).
    Defined.

    Proposition externalisation_binprod_preserves_cleaving
                (d₁ d₂ : internal_cat PB)
      : preserves_cleaving
          (cleaving_dirprod_disp_cat
             (internal_cat_to_cleaving d₁)
             (internal_cat_to_cleaving d₂))
          (internal_cat_to_cleaving
             (binprod_internal_cat BP d₁ d₂))
          (externalisation_binprod_disp_functor d₁ d₂).
    Proof.
      intros x y f yy.
      simple refine (_ ,, _).
      - unfold internal_cat_lift ; cbn.
        refine (!_).
        apply precompWithBinProductArrow.
      - use internal_morphism_over_eq.
        etrans.
        {
          apply transportf_internal_morphism_mor_eq.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          eapply idtoiso_disp_eq_to_internal_morphism.
        }
        etrans.
        {
          apply eq_to_internal_morphism_left_over.
        }
        cbn.
        unfold binprod_internal_cat_id.
        use BinProductArrowsEq.
        + rewrite !assoc'.
          rewrite BinProductPr1Commutes.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply BinProductOfArrowsPr1.
          }
          rewrite assoc.
          apply maponpaths_2.
          apply BinProductPr1Commutes.
        + rewrite !assoc'.
          rewrite BinProductPr2Commutes.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply BinProductOfArrowsPr2.
          }
          rewrite assoc.
          apply maponpaths_2.
          apply BinProductPr2Commutes.
    Qed.
    
    Definition externalisation_binprod_split_disp_functor
               (d₁ d₂ : internal_cat PB)
      : split_disp_functor
          (prod_split_disp_setcat
             (externalisation_internal_cat d₁)
             (externalisation_internal_cat d₂))
          (externalisation_internal_cat
             (binprod_internal_cat BP d₁ d₂)).
    Proof.
      use make_split_disp_functor.
      - exact (externalisation_binprod_disp_functor d₁ d₂).
      - exact (externalisation_binprod_preserves_cleaving d₁ d₂).
    Defined.

    Definition externalisation_binprod_unit
               (d₁ d₂ : internal_cat PB)
      : disp_nat_trans
          (nat_trans_id _)
          (disp_functor_identity _)
          (disp_functor_composite
             (prod_disp_functor
                (internal_functor_to_disp_functor
                   (binprod_internal_cat_pr1 BP d₁ d₂))
                (internal_functor_to_disp_functor
                   (binprod_internal_cat_pr2 BP d₁ d₂)))
             (externalisation_binprod_disp_functor d₁ d₂)).
    Proof.
      simple refine (_ ,, _).
      - refine (λ Γ x, eq_to_internal_morphism _).
        abstract
          (cbn ;
           apply BinProductArrowEta).
      - abstract
          (intros Γ₁ Γ₂ s x y f ;
           use internal_morphism_over_eq ;
           refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
           refine (_ @ !(eq_to_internal_morphism_left_over _ _)) ;
           refine (eq_to_internal_morphism_right_over _ _ @ _) ;
           cbn ;
           apply BinProductArrowEta).
    Defined.

    Definition externalisation_binprod_counit
               (d₁ d₂ : internal_cat PB)
      : disp_nat_trans
          (nat_trans_id _)
          (disp_functor_composite
             (externalisation_binprod_disp_functor d₁ d₂)
             (prod_disp_functor
                (internal_functor_to_disp_functor
                   (binprod_internal_cat_pr1 BP d₁ d₂))
                (internal_functor_to_disp_functor
                   (binprod_internal_cat_pr2 BP d₁ d₂))))
          (disp_functor_identity _).
    Proof.
      simple refine (_ ,, _).
      - refine (λ Γ x, eq_to_internal_morphism _ ,, eq_to_internal_morphism _) ; cbn.
        + apply BinProductPr1Commutes.
        + apply BinProductPr2Commutes.
      - abstract
          (intros Γ₁ Γ₂ s x y f ;
           use dirprod_paths ;
           [ refine (_ @ !(pr1_transportf _ _))
           | refine (_ @ !(pr2_transportf _ _)) ] ;
           use internal_morphism_over_eq ;
           refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
           refine (_ @ !(eq_to_internal_morphism_left_over _ _)) ;
           refine (eq_to_internal_morphism_right_over _ _ @ _) ;
           [ apply BinProductPr1Commutes
           | apply BinProductPr2Commutes ]).
    Defined.

    Definition preserves_binproduct_externalisation
      : preserves_binprods externalisation_psfunctor.
    Proof.
      use (psfunctor_preserves_binproducts
             (B₁ := bicat_with_binprod_of_internal_cat BP PB)
             (B₂ := bicat_with_binprod_of_split_disp_setcat C)).
      intros d₁ d₂ ; cbn in d₁, d₂.
      use equiv_to_adjequiv ; cbn.
      simple refine (_ ,, _).
      - simple refine (_ ,, _ ,, _).
        + exact (externalisation_binprod_split_disp_functor d₁ d₂).
        + exact (externalisation_binprod_unit d₁ d₂).
        + exact (externalisation_binprod_counit d₁ d₂).
      - split.
        * use is_invertible_2cell_split_disp_set_cat.
          intros x xx ; cbn.
          simple refine (eq_to_internal_morphism _ ,, _ ,, _).
          ** abstract
              (refine (!_) ;
               apply BinProductArrowEta).
          ** abstract
              (use internal_morphism_over_eq ;
               refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
               cbn -[internal_cat_comp_mor_over] ;
               apply (eq_to_internal_morphism_right_over
                        (d := binprod_internal_cat BP d₁ d₂))).
          ** abstract
              (use internal_morphism_over_eq ;
               refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
               cbn -[internal_cat_comp_mor_over] ;
               apply (eq_to_internal_morphism_right_over
                        (d := binprod_internal_cat BP d₁ d₂))).
        * use is_invertible_2cell_split_disp_set_cat.
          intros x xx ; cbn.
          simple refine ((eq_to_internal_morphism _ ,, eq_to_internal_morphism _) ,, _ ,, _).
          ** exact (!(BinProductPr1Commutes _ _ _ _ _ _ _)).
          ** exact (!(BinProductPr2Commutes _ _ _ _ _ _ _)).
          ** abstract
              (use dirprod_paths ;
               [ refine (_ @ !(pr1_transportf _ _))
               | refine (_ @ !(pr2_transportf _ _)) ] ;
               use internal_morphism_over_eq ;
               refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
               exact (eq_to_internal_morphism_right_over _ _)).
          ** abstract
              (use dirprod_paths ;
               [ refine (_ @ !(pr1_transportf _ _))
               | refine (_ @ !(pr2_transportf _ _)) ] ;
               use internal_morphism_over_eq ;
               refine (_ @ !(transportf_internal_morphism_mor_eq _ _ _ _)) ;
               exact (eq_to_internal_morphism_right_over _ _)).
    Defined.
  End PreservationBinProducts.
End Externalisation.
