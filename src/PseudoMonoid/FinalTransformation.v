Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import PseudoMonoid.Basics.
Require Import PseudoMonoid.ProdPseudoFunctor.

Local Open Scope cat.

Section TerminalPsTrans.
  Context {B₁ B₂ B₃ : bicat}
          (T : bifinal_obj B₃)
          (F : psfunctor B₁ B₂)
          (G : psfunctor B₂ B₃).

  Definition final_pstrans_data
    : pstrans_data (comp_psfunctor G F) (comp_psfunctor (constant _ T) F).
  Proof.
    use make_pstrans_data.
    - exact (λ x, is_bifinal_1cell_property (pr2 T) _).
    - exact (λ x y f, is_bifinal_invertible_2cell_property (pr2 T) _ _).
  Defined.

  Proposition final_pstrans_laws
    : is_pstrans final_pstrans_data.
  Proof.
    repeat split.
    - intros.
      apply is_bifinal_eq_property.
      exact (pr2 T).
    - intros.
      apply is_bifinal_eq_property.
      exact (pr2 T).
    - intros.
      apply is_bifinal_eq_property.
      exact (pr2 T).
  Qed.
  
  Definition final_pstrans
    : pstrans (comp_psfunctor G F) (comp_psfunctor (constant _ T) F).
  Proof.
    use make_pstrans.
    - exact final_pstrans_data.
    - exact final_pstrans_laws.
  Defined.
End TerminalPsTrans.
