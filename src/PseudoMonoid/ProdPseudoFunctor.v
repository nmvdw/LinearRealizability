(**

 The product of pseudofunctors

 Let `B₂` be a bicategory with binary products. We can construct the product of
 pseudofunctors `F` and `G` from some bicategory `B₁` to `B₂`. Each object `x`
 is mapped to `F x ⊗ G x`. A special instance is the diagonal, which is the
 pseudofunctor that maps `x` to `x ⊗ x`.

 Contents
 1. The data of the product of pseudofunctors
 2. The laws of the product
 3. The product of pseudofunctors
 4. The diagonal

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.

Local Open Scope cat.

Section ProdPsFunctor.
  Context {B₁ : bicat}
          {B₂ : bicat_with_binprod}
          (F G : psfunctor B₁ B₂).

  (** * 1. The data of the product of pseudofunctors *)
  Definition prod_psfunctor_id
             (x : B₁)
    : id₁ (F x ⊗ G x) ==> #F (id₁ x) ⊗₁ #G (id₁ x)
    := (pair_1cell_id_id_invertible _ _ _)^-1
       • (psfunctor_id F _ ⊗₂ psfunctor_id G _).

  Proposition prod_psfunctor_id_pr1
              (x : B₁)
    : prod_psfunctor_id x ▹ π₁
      =
      lunitor _
      • rinvunitor _
      • (_ ◃ psfunctor_id F _) 
      • (pair_1cell_pr1 _ _ _)^-1.
  Proof.
    unfold prod_psfunctor_id ; cbn.
    rewrite <- rwhisker_vcomp.
    etrans.
    {
      apply maponpaths_2.
      apply binprod_ump_2cell_pr1.
    }
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite pair_2cell_pr1.
    rewrite !vassocr.
    rewrite vcomp_linv.
    rewrite id2_left.
    apply idpath.
  Qed.

  Proposition prod_psfunctor_id_pr2
              (x : B₁)
    : prod_psfunctor_id x ▹ π₂
      =
      lunitor _
      • rinvunitor _
      • (_ ◃ psfunctor_id G _) 
      • (pair_1cell_pr2 _ _ _)^-1.
  Proof.
    unfold prod_psfunctor_id ; cbn.
    rewrite <- rwhisker_vcomp.
    etrans.
    {
      apply maponpaths_2.
      apply binprod_ump_2cell_pr2.
    }
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite pair_2cell_pr2.
    rewrite !vassocr.
    rewrite vcomp_linv.
    rewrite id2_left.
    apply idpath.
  Qed.

  Definition prod_psfunctor_comp
             {x₁ x₂ x₃ : B₁}
             (f : x₁ --> x₂)
             (g : x₂ --> x₃)
    : #F f ⊗₁ #G f · (#F g ⊗₁ #G g) ==> #F (f · g) ⊗₁ #G (f · g)
    := pair_1cell_comp _ _ _ _ _
       • (psfunctor_comp F _ _ ⊗₂ psfunctor_comp G _ _).

  Proposition prod_psfunctor_comp_pr1
              {x₁ x₂ x₃ : B₁}
              (f : x₁ --> x₂)
              (g : x₂ --> x₃)
    : prod_psfunctor_comp f g ▹ π₁
      =
      rassociator _ _ _
      • (_ ◃ pair_1cell_pr1 _ _ _)
      • lassociator _ _ _
      • (pair_1cell_pr1 _ _ _ ▹ _)
      • rassociator _ _ _
      • (_ ◃ psfunctor_comp F _ _) 
      • (pair_1cell_pr1 _ _ _)^-1.
  Proof.
    unfold prod_psfunctor_comp ; cbn.
    rewrite <- rwhisker_vcomp.
    etrans.
    {
      apply maponpaths_2.
      apply binprod_ump_2cell_pr1.
    }
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite pair_2cell_pr1.
    rewrite !vassocr.
    do 2 apply maponpaths_2.
    rewrite !vassocl.
    rewrite vcomp_linv.
    rewrite id2_right.
    apply idpath.
  Qed.

  Proposition prod_psfunctor_comp_pr2
              {x₁ x₂ x₃ : B₁}
              (f : x₁ --> x₂)
              (g : x₂ --> x₃)
    : prod_psfunctor_comp f g ▹ π₂
      =
      rassociator _ _ _
      • (_ ◃ pair_1cell_pr2 _ _ _)
      • lassociator _ _ _
      • (pair_1cell_pr2 _ _ _ ▹ _)
      • rassociator _ _ _
      • (_ ◃ psfunctor_comp G _ _) 
      • (pair_1cell_pr2 _ _ _)^-1.
  Proof.
    unfold prod_psfunctor_comp ; cbn.
    rewrite <- rwhisker_vcomp.
    etrans.
    {
      apply maponpaths_2.
      apply binprod_ump_2cell_pr2.
    }
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite pair_2cell_pr2.
    rewrite !vassocr.
    do 2 apply maponpaths_2.
    rewrite !vassocl.
    rewrite vcomp_linv.
    rewrite id2_right.
    apply idpath.
  Qed.

  Definition prod_psfunctor_data
    : psfunctor_data B₁ B₂.
  Proof.
    use make_psfunctor_data.
    - exact (λ x, F x ⊗ G x).
    - exact (λ x y f, #F f ⊗₁ #G f).
    - exact (λ x y f g θ, ##F θ ⊗₂ ##G θ).
    - exact prod_psfunctor_id.
    - exact (λ x₁ x₂ x₃ f g, prod_psfunctor_comp f g).
  Defined.

  (** * 2. The laws of the product *)
  Proposition prod_psfunctor_laws
    : psfunctor_laws prod_psfunctor_data.
  Proof.
    repeat split.
    - intros x y f ; cbn.
      rewrite !psfunctor_id2.
      apply pair_2cell_id_id.
    - intros x y f g h θ₁ θ₂ ; cbn.
      rewrite !psfunctor_vcomp.
      apply pair_2cell_comp.
    - intros x y f ; cbn -[pair_1cell_id_id_invertible psfunctor_id psfunctor_comp].
      unfold prod_psfunctor_id, prod_psfunctor_comp.
      rewrite binprod_lunitor.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !psfunctor_F_lunitor.
      rewrite !pair_2cell_comp.
      rewrite !vassocr.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite <- pair_2cell_comp.
        rewrite !vcomp_rinv.
        rewrite pair_2cell_id_id.
        apply idpath.
      }
      rewrite id2_right.
      rewrite <- binprod_rwhisker.
      rewrite !vassocl.
      rewrite <- pair_2cell_comp.
      rewrite !rwhisker_vcomp.
      rewrite !vcomp_rinv.
      rewrite !id2_rwhisker.
      rewrite pair_2cell_id_id.
      apply id2_right.
    - intros x y f ; cbn -[pair_1cell_id_id_invertible psfunctor_id psfunctor_comp].
      unfold prod_psfunctor_id, prod_psfunctor_comp.
      rewrite binprod_runitor.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !psfunctor_F_runitor.
      rewrite !pair_2cell_comp.
      rewrite !vassocr.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite <- pair_2cell_comp.
        rewrite !vcomp_rinv.
        rewrite pair_2cell_id_id.
        apply idpath.
      }
      rewrite id2_right.
      rewrite <- binprod_lwhisker.
      rewrite !vassocl.
      rewrite <- pair_2cell_comp.
      rewrite !lwhisker_vcomp.
      rewrite !vcomp_rinv.
      rewrite !lwhisker_id2.
      rewrite pair_2cell_id_id.
      apply id2_right.
    - intros x₁ x₂ x₃ x₄ f g h ; cbn -[psfunctor_comp].
      unfold prod_psfunctor_comp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- binprod_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite <- !pair_2cell_comp.
        rewrite !vassocr.
        rewrite !psfunctor_lassociator.
        rewrite !pair_2cell_comp.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite <- rwhisker_vcomp.
        rewrite !vassocl.
        rewrite <- binprod_rwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite binprod_lassociator.
      apply idpath.
    - intros x₁ x₂ x₃ f g₁ g₂ θ ; cbn -[psfunctor_comp].
      unfold prod_psfunctor_comp.
      rewrite !vassocl.
      rewrite <- pair_2cell_comp.
      rewrite !psfunctor_lwhisker.
      rewrite pair_2cell_comp.
      rewrite !vassocr.
      apply maponpaths_2.
      apply binprod_lwhisker.
    - intros x₁ x₂ x₃ f g₁ g₂ θ ; cbn -[psfunctor_comp].
      unfold prod_psfunctor_comp.
      rewrite !vassocl.
      rewrite <- pair_2cell_comp.
      rewrite !psfunctor_rwhisker.
      rewrite pair_2cell_comp.
      rewrite !vassocr.
      apply maponpaths_2.
      apply binprod_rwhisker.
  Qed.

  Definition prod_psfunctor_invertible_2cells
    : invertible_cells prod_psfunctor_data.
  Proof.
    split.
    - intro x.
      cbn ; unfold prod_psfunctor_id.
      is_iso.
      use prod_2cell_is_invertible ; is_iso ; apply property_from_invertible_2cell.
    - intros x₁ x₂ x₃ f g.
      cbn ; unfold prod_psfunctor_comp.
      is_iso.
      + apply pair_1cell_comp_invertible.
      + use prod_2cell_is_invertible ; is_iso ; apply property_from_invertible_2cell.
  Defined.

  (** * 3. The product of pseudofunctors *)
  Definition prod_psfunctor
    : psfunctor B₁ B₂.
  Proof.
    use make_psfunctor.
    - exact prod_psfunctor_data.
    - exact prod_psfunctor_laws.
    - exact prod_psfunctor_invertible_2cells.
  Defined.
End ProdPsFunctor.

(** * 4. The diagonal *)
Definition diag_psfunctor
           (B : bicat_with_binprod)
  : psfunctor B B
  := prod_psfunctor (id_psfunctor _) (id_psfunctor _).

Definition diag_psfunctor_has_prod
           {B : bicat}
           (BP : has_binprod B)
  : psfunctor B B
  := diag_psfunctor (B ,, BP).
