Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Require Import PseudoMonoid.Basics.
Require Import PseudoMonoid.ProdPseudoFunctor.
Require Import PseudoMonoid.FinalTransformation.
Require Import PseudoMonoid.Pr1Transformation.
Require Import PseudoMonoid.Pr2Transformation.
Require Import PseudoMonoid.ProdTransformation.
Require Export PseudoMonoid.PseudoMonoidOps.
Require Export PseudoMonoid.PseudoMonoidData.

Local Open Scope cat.

(** * 1. Laws of pseudomonoids *)
Definition pseudomonoid_invs_law
           {B : bicat_with_finprod}
           (x : pseudomonoid_data B)
  : UU
  := (∏ (y : B)
        (f : y --> x),
      is_invertible_2cell (pseudomonoid_lunitor x f))
     ×
     (∏ (y : B)
        (f : y --> x),
      is_invertible_2cell (pseudomonoid_runitor x f))
     ×
     (∏ (y : B)
        (f g h : y --> x),
      is_invertible_2cell (pseudomonoid_rassociator x f g h)).

Proposition isaprop_pseudomonoid_invs_law
            {B : bicat_with_finprod}
            (x : pseudomonoid_data B)
  : isaprop (pseudomonoid_invs_law x).
Proof.
  repeat (use isapropdirprod) ;
    repeat (use impred ; intro) ;
    apply isaprop_is_invertible_2cell.
Qed.
            
Definition pseudomonoid_triangle_law
           {B : bicat_with_finprod}
           (x : pseudomonoid_data B)
  : UU
  := ∏ (y : B)
       (f g : y --> x),
     pseudomonoid_rassociator x f _ g
     • pseudomonoid_lwhisker x f (pseudomonoid_lunitor x g)
     =
     pseudomonoid_rwhisker x (pseudomonoid_runitor x f) g.

Proposition isaprop_pseudomonoid_triangle_law
            {B : bicat_with_finprod}
            (x : pseudomonoid_data B)
  : isaprop (pseudomonoid_triangle_law x).
Proof.
  repeat (use impred ; intro) ; apply cellset_property.
Qed.

Definition pseudomonoid_pentagon_law
           {B : bicat_with_finprod}
           (x : pseudomonoid_data B)
  : UU
  := ∏ (y : B)
       (f g h k : y --> x),
     pseudomonoid_rassociator x (pseudomonoid_mult x f g) h k
     • pseudomonoid_rassociator x f g (pseudomonoid_mult x h k)
     =
     pseudomonoid_rwhisker x (pseudomonoid_rassociator x f g h) _
     • pseudomonoid_rassociator x f (pseudomonoid_mult x g h) k
     • pseudomonoid_lwhisker x _ (pseudomonoid_rassociator x g h k).

Proposition isaprop_pseudomonoid_pentagon_law
            {B : bicat_with_finprod}
            (x : pseudomonoid_data B)
  : isaprop (pseudomonoid_pentagon_law x).
Proof.
  repeat (use impred ; intro) ; apply cellset_property.
Qed.

Definition is_pseudomonoid
           {B : bicat_with_finprod}
           (x : pseudomonoid_data B)
  : UU
  := pseudomonoid_invs_law x
     ×
     pseudomonoid_triangle_law x
     ×
     pseudomonoid_pentagon_law x.

Proposition isaprop_is_pseudomonoid
            {B : bicat_with_finprod}
            (x : pseudomonoid_data B)
  : isaprop (is_pseudomonoid x).
Proof.
  use isapropdirprod.
  - apply isaprop_pseudomonoid_invs_law.
  - use isapropdirprod.
    + apply isaprop_pseudomonoid_triangle_law.
    + apply isaprop_pseudomonoid_pentagon_law.
Qed.

(** * 2. Laws of symmetric pseudomonoids *)
Definition is_sym_pseudomonoid_inv_law
           {B : bicat_with_finprod}
           (x : sym_pseudomonoid_data B)
  : UU
  := ∏ (y : B)
       (f g : y --> x),
     sym_pseudomonoid_braiding x f g • sym_pseudomonoid_braiding x g f = id2 _.

Proposition isaprop_is_sym_pseudomonoid_inv_law
            {B : bicat_with_finprod}
            (x : sym_pseudomonoid_data B)
  : isaprop (is_sym_pseudomonoid_inv_law x).
Proof.
  repeat (use impred ; intro) ; apply cellset_property.
Qed.

Definition is_sym_pseudomonoid_hexagon
           {B : bicat_with_finprod}
           (x : sym_pseudomonoid_data B)
  : UU
  := ∏ (y : B)
       (f g h : y --> x),
     pseudomonoid_rassociator x f g h
     • sym_pseudomonoid_braiding x f (pseudomonoid_mult x g h)
     • pseudomonoid_rassociator x g h f
     =
     pseudomonoid_rwhisker x (sym_pseudomonoid_braiding x f g) h
     • pseudomonoid_rassociator x g f h
     • pseudomonoid_lwhisker x g (sym_pseudomonoid_braiding x f h).

Proposition isaprop_is_sym_pseudomonoid_hexagon
            {B : bicat_with_finprod}
            (x : sym_pseudomonoid_data B)
  : isaprop (is_sym_pseudomonoid_hexagon x).
Proof.
  repeat (use impred ; intro) ; apply cellset_property.
Qed.

Definition is_sym_pseudomonoid
           {B : bicat_with_finprod}
           (x : sym_pseudomonoid_data B)
  : UU
  := is_pseudomonoid x
     ×
     is_sym_pseudomonoid_inv_law x
     ×
     is_sym_pseudomonoid_hexagon x.

Proposition isaprop_is_sym_pseudomonoid
            {B : bicat_with_finprod}
            (x : sym_pseudomonoid_data B)
  : isaprop (is_sym_pseudomonoid x).
Proof.
  use isapropdirprod.
  - apply isaprop_is_pseudomonoid.
  - use isapropdirprod.
    + apply isaprop_is_sym_pseudomonoid_inv_law.
    + apply isaprop_is_sym_pseudomonoid_hexagon.
Qed.

(** * 3. The bicategory of pseudomonoids and symmetric pseudomonoids *)
Section BicatPseudoMonoid.
  Context (B : bicat_with_finprod).

  Definition disp_bicat_pseudomonoid
    : disp_bicat (bicat_pseudomonoid_data B)
    := disp_fullsubbicat _ is_pseudomonoid.

  Definition bicat_pseudomonoid
    : bicat
    := total_bicat disp_bicat_pseudomonoid.

  Proposition is_univalent_2_1_disp_bicat_pseudomonoid
    : disp_univalent_2_1 disp_bicat_pseudomonoid.
  Proof.
    apply disp_fullsubbicat_univalent_2_1.
  Qed.

  Proposition is_univalent_2_0_disp_bicat_pseudomonoid
              (H : is_univalent_2 B)
    : disp_univalent_2_0 disp_bicat_pseudomonoid.
  Proof.
    use disp_univalent_2_0_fullsubbicat.
    - use is_univalent_2_bicat_pseudomonoid_data.
      exact H.
    - intro.
      apply isaprop_is_pseudomonoid.
  Qed.

  Proposition is_univalent_2_disp_bicat_pseudomonoid
              (H : is_univalent_2 B)
    : disp_univalent_2 disp_bicat_pseudomonoid.
  Proof.
    split.
    - apply is_univalent_2_0_disp_bicat_pseudomonoid.
      exact H.
    - exact is_univalent_2_1_disp_bicat_pseudomonoid.
  Qed.

  Proposition is_univalent_2_1_bicat_pseudomonoid
              (H : is_univalent_2_1 B)
    : is_univalent_2_1 bicat_pseudomonoid.
  Proof.
    use total_is_univalent_2_1.
    - use is_univalent_2_1_bicat_pseudomonoid_data.
      exact H.
    - apply is_univalent_2_1_disp_bicat_pseudomonoid.
  Qed.

  Proposition is_univalent_2_0_bicat_pseudomonoid
              (H : is_univalent_2 B)
    : is_univalent_2_0 bicat_pseudomonoid.
  Proof.
    use total_is_univalent_2_0.
    - use is_univalent_2_0_bicat_pseudomonoid_data.
      exact H.
    - apply is_univalent_2_0_disp_bicat_pseudomonoid.
      apply H.
  Qed.

  Proposition is_univalent_2_bicat_pseudomonoid
              (H : is_univalent_2 B)
    : is_univalent_2 bicat_pseudomonoid.
  Proof.
    use total_is_univalent_2.
    - apply is_univalent_2_disp_bicat_pseudomonoid.
      apply H.
    - apply is_univalent_2_bicat_pseudomonoid_data.
      exact H.
  Qed.

  Definition disp_bicat_sym_pseudomonoid
    : disp_bicat (bicat_sym_pseudomonoid_data B)
    := disp_fullsubbicat _ is_sym_pseudomonoid.

  Definition bicat_sym_pseudomonoid
    : bicat
    := total_bicat disp_bicat_sym_pseudomonoid.

  Proposition is_univalent_2_1_disp_bicat_sym_pseudomonoid
    : disp_univalent_2_1 disp_bicat_sym_pseudomonoid.
  Proof.
    apply disp_fullsubbicat_univalent_2_1.
  Qed.

  Proposition is_univalent_2_0_disp_bicat_sym_pseudomonoid
              (H : is_univalent_2 B)
    : disp_univalent_2_0 disp_bicat_sym_pseudomonoid.
  Proof.
    use disp_univalent_2_0_fullsubbicat.
    - use is_univalent_2_bicat_sym_pseudomonoid_data.
      exact H.
    - intro.
      apply isaprop_is_sym_pseudomonoid.
  Qed.

  Proposition is_univalent_2_disp_bicat_sym_pseudomonoid
              (H : is_univalent_2 B)
    : disp_univalent_2 disp_bicat_sym_pseudomonoid.
  Proof.
    split.
    - apply is_univalent_2_0_disp_bicat_sym_pseudomonoid.
      exact H.
    - exact is_univalent_2_1_disp_bicat_sym_pseudomonoid.
  Qed.

  Proposition is_univalent_2_1_bicat_sym_pseudomonoid
              (H : is_univalent_2_1 B)
    : is_univalent_2_1 bicat_sym_pseudomonoid.
  Proof.
    use total_is_univalent_2_1.
    - use is_univalent_2_1_bicat_sym_pseudomonoid_data.
      exact H.
    - apply is_univalent_2_1_disp_bicat_sym_pseudomonoid.
  Qed.

  Proposition is_univalent_2_0_bicat_sym_pseudomonoid
              (H : is_univalent_2 B)
    : is_univalent_2_0 bicat_sym_pseudomonoid.
  Proof.
    use total_is_univalent_2_0.
    - use is_univalent_2_0_bicat_sym_pseudomonoid_data.
      exact H.
    - apply is_univalent_2_0_disp_bicat_sym_pseudomonoid.
      apply H.
  Qed.

  Proposition is_univalent_2_bicat_sym_pseudomonoid
              (H : is_univalent_2 B)
    : is_univalent_2 bicat_sym_pseudomonoid.
  Proof.
    use total_is_univalent_2.
    - apply is_univalent_2_disp_bicat_sym_pseudomonoid.
      apply H.
    - apply is_univalent_2_bicat_sym_pseudomonoid_data.
      exact H.
  Qed.
End BicatPseudoMonoid.
