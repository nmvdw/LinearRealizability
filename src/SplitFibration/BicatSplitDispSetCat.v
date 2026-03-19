Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Strictness.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.

Require Import SplitFibration.SplitDispSetCat.
Require Import SplitFibration.TwoCatSplitDispSetCat.
Require Import SplitFibration.TerminalSplitFib.
Require Import SplitFibration.BinProductSplitFib.

Local Open Scope cat.

(** * 1. The strict bicategory of split fibrations over a fixed category *)
Definition strict_bicat_of_split_disp_setcat
           (C : category)
  : strict_bicat.
Proof.
  use two_cat_to_strict_bicat.
  exact (two_cat_of_split_disp_setcat C).
Defined.

(** * 2. Invertible 2-cells in this bicategory *)
Definition is_invertible_2cell_split_disp_set_cat
           {C : category}
           {D₁ D₂ : split_disp_setcat C}
           {F₁ F₂ : split_disp_functor D₁ D₂}
           {θ : disp_nat_trans (nat_trans_id _) F₁ F₂}
           (Hθ : ∏ (x : C) (xx : D₁ x), is_z_iso_disp (identity_z_iso _) (θ x xx))
  : is_invertible_2cell (C := strict_bicat_of_split_disp_setcat C) θ.
Proof.
  use make_is_invertible_2cell.
  - exact (pointwise_inverse_disp_nat_trans θ Hθ).
  - exact (pointwise_inverse_disp_nat_trans_over_id_left θ Hθ).
  - exact (pointwise_inverse_disp_nat_trans_over_id_right θ Hθ).
Defined.

Definition bifinal_bicat_of_split_disp_setcat
           (C : category)
  : bifinal_obj (strict_bicat_of_split_disp_setcat C).
Proof.
  simple refine (_ ,, _).
  - exact (terminal_split_disp_setcat C).
  - split.
    + intros D.
      exact (disp_functor_to_terminal_split_disp_setcat C D).
    + intros D.
      split.
      * intros F₁ F₂.
        exact (disp_functor_to_terminal_split_disp_setcat_nat_trans C F₁ F₂).
      * intros F₁ F₂ θ₁ θ₂.
        apply disp_functor_to_terminal_split_disp_setcat_nat_trans_unique.
Defined.

Section BinProduct.
  Context {C : category}
          (D₁ D₂ : strict_bicat_of_split_disp_setcat C).

  Definition bicat_of_split_disp_setcat_binprod_cone
    : binprod_cone D₁ D₂.
  Proof.
    use make_binprod_cone.
    - exact (prod_split_disp_setcat D₁ D₂).
    - exact (prod_split_disp_setcat_pr1 D₁ D₂).
    - exact (prod_split_disp_setcat_pr2 D₁ D₂).
  Defined.

  Definition bicat_of_split_disp_setcat_binprod_1cell_pr1
             (c : binprod_cone D₁ D₂)
    : invertible_2cell
        (C := strict_bicat_of_split_disp_setcat C)
        (prod_split_disp_functor _ _ (binprod_cone_pr1 c) (binprod_cone_pr2 c)
         · prod_split_disp_setcat_pr1 D₁ D₂)
        (binprod_cone_pr1 c).
  Proof.
    use idtoiso_2_1.
    apply prod_split_disp_functor_pr1.
  Defined.

  Definition bicat_of_split_disp_setcat_binprod_1cell_pr2
             (c : binprod_cone D₁ D₂)
    : invertible_2cell
        (C := strict_bicat_of_split_disp_setcat C)
        (prod_split_disp_functor _ _ (binprod_cone_pr1 c) (binprod_cone_pr2 c)
         · prod_split_disp_setcat_pr2 D₁ D₂)
        (binprod_cone_pr2 c).
  Proof.
    use idtoiso_2_1.
    apply prod_split_disp_functor_pr2.
  Defined.

  Definition bicat_of_split_disp_setcat_binprod_1cell
             (c : binprod_cone D₁ D₂)
    : binprod_1cell c bicat_of_split_disp_setcat_binprod_cone.
  Proof.
    use make_binprod_1cell.
    - exact (prod_split_disp_functor _ _ (binprod_cone_pr1 c) (binprod_cone_pr2 c)).
    - exact (bicat_of_split_disp_setcat_binprod_1cell_pr1 c).
    - exact (bicat_of_split_disp_setcat_binprod_1cell_pr2 c).
  Defined.
End BinProduct.

Definition binprod_bicat_of_split_disp_setcat
           (C : category)
  : has_binprod (strict_bicat_of_split_disp_setcat C).
Proof.
  intros D₁ D₂.
  simple refine (_ ,, _).
  - exact (bicat_of_split_disp_setcat_binprod_cone D₁ D₂).
  - split.
    + exact (bicat_of_split_disp_setcat_binprod_1cell D₁ D₂).
    + intros E FF GG θ₁ θ₂.
      use iscontraprop1.
      * exact (prod_split_disp_nat_trans_unique D₁ D₂ θ₁ θ₂).
      * simple refine (_ ,, _ ,, _).
        ** exact (prod_split_disp_nat_trans D₁ D₂ θ₁ θ₂).
        ** exact (prod_split_disp_nat_trans_pr1 D₁ D₂ θ₁ θ₂).
        ** exact (prod_split_disp_nat_trans_pr2 D₁ D₂ θ₁ θ₂).
Defined.

Definition bicat_with_binprod_of_split_disp_setcat
           (C : category)
  : bicat_with_binprod
  := _ ,, binprod_bicat_of_split_disp_setcat C.
