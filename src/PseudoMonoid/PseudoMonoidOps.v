Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.

Require Import PseudoMonoid.Basics.
Require Import PseudoMonoid.ProdPseudoFunctor.

Local Open Scope cat.
         
Section PseudoMonoidOps.
  Context (B : bicat_with_finprod).

  Definition disp_bicat_pseudomonoid_unit
    : disp_bicat B
    := disp_alg_bicat (constant B (bicat_with_finprod_final B)).

  Definition disp_bicat_pseudomonoid_mult
    : disp_bicat B
    := disp_alg_bicat (diag_psfunctor B).

  Definition disp_bicat_pseudomonoid_ops
    : disp_bicat B
    := disp_dirprod_bicat
         disp_bicat_pseudomonoid_unit
         disp_bicat_pseudomonoid_mult.

  Proposition is_univalent_2_1_disp_bicat_pseudomonoid_ops
    : disp_univalent_2_1 disp_bicat_pseudomonoid_ops.
  Proof.
    use is_univalent_2_1_dirprod_bicat.
    - apply disp_alg_bicat_univalent_2_1.
    - apply disp_alg_bicat_univalent_2_1.
  Qed.

  Proposition is_univalent_2_0_disp_bicat_pseudomonoid_ops
              (H : is_univalent_2_1 B)
    : disp_univalent_2_0 disp_bicat_pseudomonoid_ops.
  Proof.
    use is_univalent_2_0_dirprod_bicat.
    - exact H.
    - split.
      + apply disp_alg_bicat_univalent_2_0.
        exact H.
      + apply disp_alg_bicat_univalent_2_1.
    - split.
      + apply disp_alg_bicat_univalent_2_0.
        exact H.
      + apply disp_alg_bicat_univalent_2_1.
  Qed.

  Proposition is_univalent_2_disp_bicat_pseudomonoid_ops
              (H : is_univalent_2_1 B)
    : disp_univalent_2 disp_bicat_pseudomonoid_ops.
  Proof.
    split.
    - apply is_univalent_2_0_disp_bicat_pseudomonoid_ops.
      exact H.
    - exact is_univalent_2_1_disp_bicat_pseudomonoid_ops.
  Qed.

  Definition bicat_pseudomonoid_ops
    : bicat
    := total_bicat disp_bicat_pseudomonoid_ops.

  Proposition is_univalent_2_1_bicat_pseudomonoid_ops
              (H : is_univalent_2_1 B)
    : is_univalent_2_1 bicat_pseudomonoid_ops.
  Proof.
    use total_is_univalent_2_1.
    - exact H.
    - apply is_univalent_2_1_disp_bicat_pseudomonoid_ops.
  Qed.

  Proposition is_univalent_2_0_bicat_pseudomonoid_ops
              (H : is_univalent_2 B)
    : is_univalent_2_0 bicat_pseudomonoid_ops.
  Proof.
    use total_is_univalent_2_0.
    - apply H.
    - apply is_univalent_2_0_disp_bicat_pseudomonoid_ops.
      apply H.
  Qed.

  Proposition is_univalent_2_bicat_pseudomonoid_ops
              (H : is_univalent_2 B)
    : is_univalent_2 bicat_pseudomonoid_ops.
  Proof.
    use total_is_univalent_2.
    - apply is_univalent_2_disp_bicat_pseudomonoid_ops.
      apply H.
    - exact H.
  Qed.
End PseudoMonoidOps.

Definition pseudomonoid_ops
           (B : bicat_with_finprod)
  : UU
  := bicat_pseudomonoid_ops B.

Definition make_pseudomonoid_ops
           {B : bicat_with_finprod}
           (x : B)
           (u : pr1 (bicat_with_finprod_final B) --> x)
           (m : x ⊗ x --> x)
  : pseudomonoid_ops B
  := x ,, u ,, m.

Coercion pseudomonoid_ops_carrier
         {B : bicat_with_finprod}
         (x : pseudomonoid_ops B)
  : B
  := pr1 x.
           
Definition pseudomonoid_unit_op
           {B : bicat_with_finprod}
           (x : pseudomonoid_ops B)
  : bicat_with_finprod_final B --> x
  := pr12 x.

Definition pseudomonoid_unit
           {B : bicat_with_finprod}
           (x : pseudomonoid_ops B)
           (y : B)
  : y --> x
  := is_bifinal_1cell_property (pr212 B) _ · pseudomonoid_unit_op x.
             
Definition pseudomonoid_mult_op
           {B : bicat_with_finprod}
           (x : pseudomonoid_ops B)
  : x ⊗ x --> x
  := pr22 x.

Definition pseudomonoid_mult
           {B : bicat_with_finprod}
           (x : pseudomonoid_ops B)
           {y : B}
           (f g : y --> x)
  : y --> x
  := ⟨ f , g ⟩ · pseudomonoid_mult_op x.

Definition pseudomonoid_lwhisker
           {B : bicat_with_finprod}
           (x : pseudomonoid_ops B)
           {y : B}
           (f : y --> x)
           {g₁ g₂ : y --> x}
           (θ : g₁ ==> g₂)
  : pseudomonoid_mult x f g₁ ==> pseudomonoid_mult x f g₂
  := ⟪ id2 _ , θ ⟫ ▹ _.

Definition pseudomonoid_rwhisker
           {B : bicat_with_finprod}
           (x : pseudomonoid_ops B)
           {y : B}
           {f₁ f₂ : y --> x}
           (θ : f₁ ==> f₂)
           (g : y --> x)
  : pseudomonoid_mult x f₁ g ==> pseudomonoid_mult x f₂ g
  := ⟪ θ , id2 _ ⟫ ▹ _.
