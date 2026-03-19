Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Strictness.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.

Require Import InternalCategories.InternalCat.
Require Import InternalCategories.InternalFunctor.
Require Import InternalCategories.InternalNatTrans.
Require Import InternalCategories.CatOfInternalCat.
Require Import InternalCategories.TwoCatOfInternalCat.
Require Import InternalCategories.TerminalInternalCat.
Require Import InternalCategories.ProdInternalCat.

Local Open Scope cat.

(** * 1. The strict bicategory of internal categories *)
Definition strict_bicat_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : strict_bicat.
Proof.
  use two_cat_to_strict_bicat.
  exact (two_cat_of_internal_cat PB).
Defined.

(** * 2. The terminal object in the bicategory of internal categories *)
Definition bifinal_bicat_of_internal_cat
           {C : category}
           (T : Terminal C)
           (PB : Pullbacks C)
  : bifinal_obj (strict_bicat_of_internal_cat PB).
Proof.
  simple refine (_ ,, _).
  - exact (terminal_internal_cat T PB).
  - split.
    + intros d.
      exact (internal_functor_to_terminal T PB d).
    + intros d.
      split.
      * intros f₁ f₂.
        exact (internal_functor_to_terminal_nat_trans T PB f₁ f₂).
      * intros f₁ f₂ θ₁ θ₂.
        exact (internal_functor_to_terminal_nat_trans_eq T PB θ₁ θ₂).
Defined.

(** * 3. Binary products in the bicategory of internal categories *)
Section BinProduct.
  Context {C : category}
          (BP : BinProducts C)
          {PB : Pullbacks C}
          (d₁ d₂ : strict_bicat_of_internal_cat PB).

  Definition bicat_of_internal_cat_binprod_cone
    : binprod_cone d₁ d₂.
  Proof.
    use make_binprod_cone.
    - exact (binprod_internal_cat BP d₁ d₂).
    - exact (binprod_internal_cat_pr1 BP d₁ d₂).
    - exact (binprod_internal_cat_pr2 BP d₁ d₂).
  Defined.

  Definition bicat_of_internal_cat_binprod_1cell_pr1
             (c : binprod_cone d₁ d₂)
    : invertible_2cell
        (C := strict_bicat_of_internal_cat PB)
        (comp_internal_functor
           (binprod_internal_cat_pair BP d₁ d₂ (binprod_cone_pr1 c) (binprod_cone_pr2 c))
           (binprod_internal_cat_pr1 BP d₁ d₂))
        (binprod_cone_pr1 c).
  Proof.
    use idtoiso_2_1.
    apply binprod_internal_cat_pair_pr1.
  Defined.

  Definition bicat_of_internal_cat_binprod_1cell_pr2
             (c : binprod_cone d₁ d₂)
    : invertible_2cell
        (C := strict_bicat_of_internal_cat PB)
        (comp_internal_functor
           (binprod_internal_cat_pair BP d₁ d₂ (binprod_cone_pr1 c) (binprod_cone_pr2 c))
           (binprod_internal_cat_pr2 BP d₁ d₂))
        (binprod_cone_pr2 c).
  Proof.
    use idtoiso_2_1.
    apply binprod_internal_cat_pair_pr2.
  Defined.

  Definition bicat_of_internal_cat_binprod_1cell
             (c : binprod_cone d₁ d₂)
    : binprod_1cell c bicat_of_internal_cat_binprod_cone.
  Proof.
    use make_binprod_1cell.
    - exact (binprod_internal_cat_pair BP d₁ d₂ (binprod_cone_pr1 c) (binprod_cone_pr2 c)).
    - exact (bicat_of_internal_cat_binprod_1cell_pr1 c).
    - exact (bicat_of_internal_cat_binprod_1cell_pr2 c).
  Defined.
End BinProduct.

Definition binprod_bicat_of_internal_cat
           {C : category}
           (BP : BinProducts C)
           (PB : Pullbacks C)
  : has_binprod (strict_bicat_of_internal_cat PB).
Proof.
  intros d₁ d₂.
  simple refine (_ ,, _).
  - exact (bicat_of_internal_cat_binprod_cone BP d₁ d₂).
  - split.
    + exact (bicat_of_internal_cat_binprod_1cell BP d₁ d₂).
    + intros c f₁ f₂ θ₁ θ₂.
      use make_iscontr.
      * simple refine (_ ,, _ ,, _).
        ** exact (binprod_internal_cat_nat_trans BP d₁ d₂ θ₁ θ₂).
        ** exact (binprod_internal_cat_nat_trans_pr1 BP d₁ d₂ θ₁ θ₂).
        ** exact (binprod_internal_cat_nat_trans_pr2 BP d₁ d₂ θ₁ θ₂).
      * abstract
          (intros (τ & p₁ & p₂) ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
           exact (binprod_internal_cat_nat_trans_unique _ _ _ _ _ p₁ p₂)).
Defined.

Definition bicat_with_binprod_of_internal_cat
           {C : category}
           (BP : BinProducts C)
           (PB : Pullbacks C)
  : bicat_with_binprod
  := _ ,, binprod_bicat_of_internal_cat BP PB.
