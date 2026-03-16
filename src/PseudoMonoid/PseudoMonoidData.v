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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.AlgebraMap.

Require Import PseudoMonoid.Basics.
Require Import PseudoMonoid.ProdPseudoFunctor.
Require Import PseudoMonoid.FinalTransformation.
Require Import PseudoMonoid.Pr1Transformation.
Require Import PseudoMonoid.Pr2Transformation.
Require Import PseudoMonoid.ProdTransformation.
Require Export PseudoMonoid.PseudoMonoidOps.

Local Open Scope cat.

Section PseudoMonoidData.
  Context (B : bicat_with_finprod).

  (** * 1. Some useful pseudotransformations for defining pseudomonoids *)
  Definition pseudomonoid_var
             (S : psfunctor B B)
    : pstrans
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           S (pr1_psfunctor _))
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           S (pr1_psfunctor _))
    := id₁ _.
  
  Definition unit_map_data
    : pstrans_data
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           (constant B (bicat_with_finprod_final B))
           (pr1_psfunctor _))
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           (id_psfunctor _)
           (pr1_psfunctor _)).
  Proof.
    use make_pstrans_data.
    - exact (λ x, pr12 x).
    - exact (λ x y f, pr12 f).
  Defined.

  Definition unit_map_is_pstrans
    : is_pstrans unit_map_data.
  Proof.
    repeat split ; cbn.
    - intros X Y f g α.
      apply α.
    - intros ; cbn.
      rewrite !id2_rwhisker.
      rewrite !id2_right.
      rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - intros ; cbn.
      rewrite !id2_right.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
  Qed.

  Definition unit_map
    : pstrans
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           (constant B (bicat_with_finprod_final B))
           (pr1_psfunctor _))
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           (id_psfunctor _)
           (pr1_psfunctor _)).
  Proof.
    use make_pstrans.
    - exact unit_map_data.
    - exact unit_map_is_pstrans.
  Defined.

  Definition mult_map_data
    : pstrans_data
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           (diag_psfunctor B)
           (pr1_psfunctor _))
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           (id_psfunctor _)
           (pr1_psfunctor _)).
  Proof.
    use make_pstrans_data.
    - exact (λ x, pr22 x).
    - exact (λ x y f, pr22 f).
  Defined.

  Definition mult_map_is_pstrans
    : is_pstrans mult_map_data.
  Proof.
    repeat split.
    - intros X Y f g α.
      apply α.
    - intros ; cbn.
      rewrite !id2_right.
      rewrite lwhisker_id2.
      rewrite !id2_left.
      rewrite pair_2cell_id_id.
      rewrite id2_right.
      apply idpath.
    - intros ; cbn.
      rewrite !id2_right.
      rewrite lwhisker_id2.
      rewrite !id2_left.
      rewrite pair_2cell_id_id.
      rewrite id2_right.
      apply idpath.
  Qed.

  Definition mult_map
    : pstrans
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           (diag_psfunctor B)
           (pr1_psfunctor _))
        (@comp_psfunctor
           (bicat_pseudomonoid_ops B) _ _
           (id_psfunctor _)
           (pr1_psfunctor _)).
  Proof.
    use make_pstrans.
    - exact mult_map_data.
    - exact mult_map_is_pstrans.
  Defined.

  (** * 2. The left unitor of pseudomonoids *)
  Definition disp_bicat_pseudomonoid_lunitor
    : disp_bicat (bicat_pseudomonoid_ops B).
  Proof.
    use add_cell_disp_cat.
    - exact (id_psfunctor B).
    - exact (id_psfunctor B).
    - refine (_ · mult_map).
      use prod_pstrans.
      + exact (final_pstrans _ _ _ · unit_map).
      + apply pseudomonoid_var.
    - apply pseudomonoid_var.
  Defined.

  (** * 3. The right unitor of pseudomonoids *)
  Definition disp_bicat_pseudomonoid_runitor
    : disp_bicat (bicat_pseudomonoid_ops B).
  Proof.
    use add_cell_disp_cat.
    - exact (id_psfunctor B).
    - exact (id_psfunctor B).
    - refine (_ · mult_map).
      use prod_pstrans.
      + apply pseudomonoid_var.
      + exact (final_pstrans _ _ _ · unit_map).
    - apply pseudomonoid_var.
  Defined.

  (** * 4. The associator of pseudomonoids *)
  Definition disp_bicat_pseudomonoid_associator
    : disp_bicat (bicat_pseudomonoid_ops B).
  Proof.
    use add_cell_disp_cat.
    - exact (prod_psfunctor
               (prod_psfunctor (id_psfunctor B) (id_psfunctor B))
               (id_psfunctor B)).
    - exact (id_psfunctor B).
    - refine (_ · mult_map).
      use prod_pstrans.
      + refine (pr1_pstrans _ _ _ · _).
        apply mult_map.
      + apply pr2_pstrans.
    - refine (_ · mult_map).
      use prod_pstrans.
      + exact (pr1_pstrans _ _ _ · pr1_pstrans _ _ _).
      + refine (_ · mult_map).
        use prod_pstrans.
        * exact (pr1_pstrans _ _ _ · pr2_pstrans _ _ _).
        * exact (pr2_pstrans _ _ _).
  Defined.

  (** * 4. The braiding of pseudomonoids *)
  Definition disp_bicat_pseudomonoid_symmetry
    : disp_bicat (bicat_pseudomonoid_ops B).
  Proof.
    use add_cell_disp_cat.
    - exact (diag_psfunctor _).
    - exact (id_psfunctor B).
    - exact mult_map.
    - refine (_ · mult_map).
      use prod_pstrans.
      + exact (pr2_pstrans _ _ _).
      + exact (pr1_pstrans _ _ _).
  Defined.

  (** * 6. The data of pseudomonoids *)
  Definition disp_bicat_pseudomonoid_data
    : disp_bicat (bicat_pseudomonoid_ops B)
    := disp_dirprod_bicat
         disp_bicat_pseudomonoid_lunitor
         (disp_dirprod_bicat
            disp_bicat_pseudomonoid_runitor
            disp_bicat_pseudomonoid_associator).

  Proposition is_univalent_2_1_disp_bicat_pseudomonoid_data
    : disp_univalent_2_1 disp_bicat_pseudomonoid_data.
  Proof.
    use is_univalent_2_1_dirprod_bicat.
    - apply add_cell_disp_cat_univalent_2_1.
    - use is_univalent_2_1_dirprod_bicat.
      + apply add_cell_disp_cat_univalent_2_1.
      + apply add_cell_disp_cat_univalent_2_1.
  Qed.

  Proposition is_univalent_2_0_disp_bicat_pseudomonoid_data
              (H : is_univalent_2_1 B)
    : disp_univalent_2_0 disp_bicat_pseudomonoid_data.
  Proof.
    use is_univalent_2_0_dirprod_bicat.
    - use is_univalent_2_1_bicat_pseudomonoid_ops.
      exact H.
    - use add_cell_disp_cat_univalent_2.
      + exact H.
      + apply is_univalent_2_1_disp_bicat_pseudomonoid_ops.
    - use is_univalent_2_dirprod_bicat.
      + use is_univalent_2_1_bicat_pseudomonoid_ops.
        exact H.
      + use add_cell_disp_cat_univalent_2.
        * exact H.
        * apply is_univalent_2_1_disp_bicat_pseudomonoid_ops.
      + use add_cell_disp_cat_univalent_2.
        * exact H.
        * apply is_univalent_2_1_disp_bicat_pseudomonoid_ops.
  Qed.

  Proposition is_univalent_2_disp_bicat_pseudomonoid_data
              (H : is_univalent_2_1 B)
    : disp_univalent_2 disp_bicat_pseudomonoid_data.
  Proof.
    split.
    - apply is_univalent_2_0_disp_bicat_pseudomonoid_data.
      exact H.
    - exact is_univalent_2_1_disp_bicat_pseudomonoid_data.
  Qed.

  (** * 7. The bicategory of pseudomonoids *)
  Definition bicat_pseudomonoid_data
    : bicat
    := total_bicat disp_bicat_pseudomonoid_data.

  Proposition is_univalent_2_1_bicat_pseudomonoid_data
              (H : is_univalent_2_1 B)
    : is_univalent_2_1 bicat_pseudomonoid_data.
  Proof.
    use total_is_univalent_2_1.
    - use is_univalent_2_1_bicat_pseudomonoid_ops.
      exact H.
    - apply is_univalent_2_1_disp_bicat_pseudomonoid_data.
  Qed.

  Proposition is_univalent_2_0_bicat_pseudomonoid_data
              (H : is_univalent_2 B)
    : is_univalent_2_0 bicat_pseudomonoid_data.
  Proof.
    use total_is_univalent_2_0.
    - use is_univalent_2_0_bicat_pseudomonoid_ops.
      exact H.
    - apply is_univalent_2_0_disp_bicat_pseudomonoid_data.
      apply H.
  Qed.

  Proposition is_univalent_2_bicat_pseudomonoid_data
              (H : is_univalent_2 B)
    : is_univalent_2 bicat_pseudomonoid_data.
  Proof.
    use total_is_univalent_2.
    - apply is_univalent_2_disp_bicat_pseudomonoid_data.
      apply H.
    - apply is_univalent_2_bicat_pseudomonoid_ops.
      exact H.
  Qed.

  (** * 8. The data of symmetric pseudomonoids *)
  Definition disp_bicat_sym_pseudomonoid_data
    : disp_bicat (bicat_pseudomonoid_ops B)
    := disp_dirprod_bicat
         disp_bicat_pseudomonoid_data
         disp_bicat_pseudomonoid_symmetry.

  Proposition is_univalent_2_1_disp_bicat_sym_pseudomonoid_data
    : disp_univalent_2_1 disp_bicat_sym_pseudomonoid_data.
  Proof.
    use is_univalent_2_1_dirprod_bicat.
    - exact is_univalent_2_1_disp_bicat_pseudomonoid_data.
    - apply add_cell_disp_cat_univalent_2_1.
  Qed.

  Proposition is_univalent_2_0_disp_bicat_sym_pseudomonoid_data
              (H : is_univalent_2_1 B)
    : disp_univalent_2_0 disp_bicat_sym_pseudomonoid_data.
  Proof.
    use is_univalent_2_0_dirprod_bicat.
    - use is_univalent_2_1_bicat_pseudomonoid_ops.
      exact H.
    - use is_univalent_2_disp_bicat_pseudomonoid_data.
      exact H.
    - use add_cell_disp_cat_univalent_2.
      + exact H.
      + apply is_univalent_2_1_disp_bicat_pseudomonoid_ops.
  Qed.

  Proposition is_univalent_2_disp_bicat_sym_pseudomonoid_data
              (H : is_univalent_2_1 B)
    : disp_univalent_2 disp_bicat_sym_pseudomonoid_data.
  Proof.
    split.
    - apply is_univalent_2_0_disp_bicat_sym_pseudomonoid_data.
      exact H.
    - exact is_univalent_2_1_disp_bicat_sym_pseudomonoid_data.
  Qed.

  (** * 9. The bicategory of symmetric pseudomonoids *)
  Definition bicat_sym_pseudomonoid_data
    : bicat
    := total_bicat disp_bicat_sym_pseudomonoid_data.

  Proposition is_univalent_2_1_bicat_sym_pseudomonoid_data
              (H : is_univalent_2_1 B)
    : is_univalent_2_1 bicat_sym_pseudomonoid_data.
  Proof.
    use total_is_univalent_2_1.
    - use is_univalent_2_1_bicat_pseudomonoid_ops.
      exact H.
    - apply is_univalent_2_1_disp_bicat_sym_pseudomonoid_data.
  Qed.

  Proposition is_univalent_2_0_bicat_sym_pseudomonoid_data
              (H : is_univalent_2 B)
    : is_univalent_2_0 bicat_sym_pseudomonoid_data.
  Proof.
    use total_is_univalent_2_0.
    - use is_univalent_2_0_bicat_pseudomonoid_ops.
      exact H.
    - apply is_univalent_2_0_disp_bicat_sym_pseudomonoid_data.
      apply H.
  Qed.

  Proposition is_univalent_2_bicat_sym_pseudomonoid_data
              (H : is_univalent_2 B)
    : is_univalent_2 bicat_sym_pseudomonoid_data.
  Proof.
    use total_is_univalent_2.
    - apply is_univalent_2_disp_bicat_sym_pseudomonoid_data.
      apply H.
    - apply is_univalent_2_bicat_pseudomonoid_ops.
      exact H.
  Qed.
End PseudoMonoidData.

(** * 10. Accessors for (symmetric) pseudomonoids *)
Definition pseudomonoid_data
           (B : bicat_with_finprod)
  : UU
  := bicat_pseudomonoid_data B.

Definition make_pseudomonoid_data
           {B : bicat_with_finprod}
           (x : pseudomonoid_ops B)
           (l :  pseudomonoid_mult x (pseudomonoid_unit _ _) (id₁ _) ==> id₁ _)
           (r :  pseudomonoid_mult x (id₁ _) (pseudomonoid_unit _ _) ==> id₁ _)
           (a : ⟨ π₁ · pseudomonoid_mult_op x, π₂ ⟩ · pseudomonoid_mult_op x
                ==>
                ⟨ π₁ · π₁, ⟨ π₁ · π₂, π₂ ⟩ · pseudomonoid_mult_op x ⟩
                · pseudomonoid_mult_op x)
  : pseudomonoid_data B
  := x ,, l ,, r ,, a.
  
Coercion pseudomonoid_data_to_ops
         {B : bicat_with_finprod}
         (x : pseudomonoid_data B)
  : pseudomonoid_ops B
  := pr1 x.

Definition pseudomonoid_lunitor
           {B : bicat_with_finprod}
           (x : pseudomonoid_data B)
           {y : B}
           (f : y --> x)
  : pseudomonoid_mult x (pseudomonoid_unit _ _) f ==> f.
Proof.
  refine ((_ • (precomp_prod_1cell_invertible _ _ _ _)^-1 ▹ _)
          • rassociator _ _ _
          • (_ ◃ pr12 x)
          • runitor _).
  cbn.
  refine (⟪ (is_bifinal_2cell_property _ _ _ _ ▹ _) • rassociator _ _ _ , rinvunitor _ ⟫).
  exact (pr212 B).
Defined.

Definition pseudomonoid_runitor
           {B : bicat_with_finprod}
           (x : pseudomonoid_data B)
           {y : B}
           (f : y --> x)
  : pseudomonoid_mult x f (pseudomonoid_unit _ _) ==> f.
Proof.
  refine ((_ • (precomp_prod_1cell_invertible _ _ _ _)^-1 ▹ _)
          • rassociator _ _ _
          • (_ ◃ pr122 x)
          • runitor _).
  cbn.
  refine (⟪ rinvunitor _ , (is_bifinal_2cell_property _ _ _ _ ▹ _) • rassociator _ _ _ ⟫).
  exact (pr212 B).
Defined.

Definition pseudomonoid_rassociator
           {B : bicat_with_finprod}
           (x : pseudomonoid_data B)
           {y : B}
           (f g h : y --> x)
  : pseudomonoid_mult x (pseudomonoid_mult x f g) h
    ==>
    pseudomonoid_mult x f (pseudomonoid_mult x g h).
Proof.
  refine (_ • (⟨ ⟨ f , g ⟩ , h ⟩ ◃ pr222 x) • _) ; cbn.
  - refine ((_ ▹ _) • rassociator _ _ _).
    refine (⟪ _ , _ ⟫ • (precomp_prod_1cell_invertible _ _ _ _)^-1).
    + unfold pseudomonoid_mult ; cbn.
      refine ((_ ▹ _) • rassociator _ _ _).
      exact ((prod_1cell_pr1 _ _ _)^-1).
    + unfold pseudomonoid_mult ; cbn.
      exact ((prod_1cell_pr2 _ _ _)^-1).
  - refine (lassociator _ _ _ • (_ ▹ _)).
    refine (precomp_prod_1cell_invertible _ _ _ _ • ⟪ _ , _ ⟫).
    + refine (lassociator _ _ _ • _).
      refine ((prod_1cell_pr1 _ _ _ ▹ _) • _).
      exact (prod_1cell_pr1 _ _ _).
    + refine (lassociator _ _ _ • (_ ▹ _)).
      refine (precomp_prod_1cell_invertible _ _ _ _ • ⟪ _ , _ ⟫).
      * refine (lassociator _ _ _ • _).
        refine ((prod_1cell_pr1 _ _ _ ▹ _) • _).
        exact (prod_1cell_pr2 _ _ _).
      * exact (prod_1cell_pr2 _ _ _).
Defined.

Definition sym_pseudomonoid_data
           (B : bicat_with_finprod)
  : UU
  := bicat_sym_pseudomonoid_data B.

Coercion sym_pseudomonoid_data_to_data
         {B : bicat_with_finprod}
         (x : sym_pseudomonoid_data B)
  : pseudomonoid_data B
  := make_pseudomonoid_data
       (pr1 x)
       (pr112 x)
       (pr1 (pr212 x))
       (pr2 (pr212 x)).

Definition sym_pseudomonoid_braiding
           {B : bicat_with_finprod}
           (x : sym_pseudomonoid_data B)
           {y : B}
           (f g : y --> x)
  : pseudomonoid_mult x f g
    ==>
    pseudomonoid_mult x g f.
Proof.
  refine ((_ ◃ pr22 x)
          • lassociator _ _ _
          • (_ ▹ _)).
  cbn.
  refine (precomp_prod_1cell_invertible _ _ _ _ • ⟪ _ , _ ⟫).
  - exact (prod_1cell_pr2 _ _ _).
  - exact (prod_1cell_pr1 _ _ _).
Defined.
