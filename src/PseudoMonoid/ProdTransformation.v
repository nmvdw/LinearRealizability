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
Require Export PseudoMonoid.ProdPseudoFunctor.
Require Import PseudoMonoid.ProdTransformation.Data.
Require Import PseudoMonoid.ProdTransformation.Naturality.
Require Import PseudoMonoid.ProdTransformation.Identity.
Require Import PseudoMonoid.ProdTransformation.Composition.

Local Open Scope cat.

Proposition prod_pstrans_laws
            {B₁ B₂ : bicat}
            {B₃ : bicat_with_binprod}
            {F G H : psfunctor B₂ B₃}
            (K : psfunctor B₁ B₂)
            (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
            (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K))
  : is_pstrans (prod_pstrans_data K τ₁ τ₂).
Proof.
  repeat split.
  - intros x y f g θ.
    exact (prod_pstrans_naturality K τ₁ τ₂ θ).
  - intros x.
    exact (prod_pstrans_id K τ₁ τ₂ x).
  - intros x y z f g.
    exact (prod_pstrans_comp K τ₁ τ₂ f g).
Qed.
  
Definition prod_pstrans
           {B₁ B₂ : bicat}
           {B₃ : bicat_with_binprod}
           {F G H : psfunctor B₂ B₃}
           (K : psfunctor B₁ B₂)
           (τ₁ : pstrans (comp_psfunctor H K) (comp_psfunctor F K))
           (τ₂ : pstrans (comp_psfunctor H K) (comp_psfunctor G K))
  : pstrans (comp_psfunctor H K) (comp_psfunctor (prod_psfunctor F G) K).
Proof.
  use make_pstrans.
  - exact (prod_pstrans_data K τ₁ τ₂).
  - exact (prod_pstrans_laws K τ₁ τ₂).
Defined.
