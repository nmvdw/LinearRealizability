Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.
Require Import UniMath.Bicategories.Core.AdjointUnique.

Local Open Scope cat.

Proposition adjoint_unique_map_unique_cell
            {B : bicat}
            {x y : B}
            {l : x --> y}
            (A₁ A₂ : left_adjoint l)
            (r₁ := left_adjoint_right_adjoint A₁)
            (r₂ := left_adjoint_right_adjoint A₂)
            (η₁ := left_adjoint_unit A₁)
            (η₂ := left_adjoint_unit A₂)
            (ε₁ := left_adjoint_counit A₁)
            (ε₂ := left_adjoint_counit A₂)
            {θ : r₁ ==> r₂}
            (p : η₁ • (l ◃ θ) = η₂)
  : adjoint_unique_map _ A₁ A₂ = θ.
Proof.
  unfold adjoint_unique_map.
  fold r₁ r₂ η₁ η₂ ε₁ ε₂.
  rewrite <- p.
  rewrite <- !lwhisker_vcomp.
  etrans.
  {
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite !vassocr.
    rewrite lwhisker_lwhisker.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite <- vcomp_whisker.
    rewrite !vassocl.
    rewrite vcomp_lunitor.
    apply idpath.
  }
  rewrite !vassocr.
  refine (_ @ id2_left _).
  apply maponpaths_2.
  exact (internal_triangle2 A₁).
Qed.

Proposition lwhisker_adjoint_unique_map
            {B : bicat}
            {x y z : B}
            {l₁ : x --> y}
            {l₂ : y --> z}
            (A₁ A₁' : left_adjoint l₁)
            (A₂ : left_adjoint l₂)
            (r₁ := left_adjoint_right_adjoint A₁)
            (r₁' := left_adjoint_right_adjoint A₁')
            (r₂ := left_adjoint_right_adjoint A₂)
            (η₁ := left_adjoint_unit A₁)
            (η₁' := left_adjoint_unit A₁')
            (η₂ := left_adjoint_unit A₂)
            (ε₁ := left_adjoint_counit A₁)
            (ε₁' := left_adjoint_counit A₁')
            (ε₂ := left_adjoint_counit A₂)
  : r₂ ◃ (adjoint_unique_map _ A₁ A₁')
    =
    adjoint_unique_map _ (comp_left_adjoint _ _ A₁ A₂) (comp_left_adjoint _ _ A₁' A₂).
Proof.
  refine (!_).
  refine (adjoint_unique_map_unique_cell
            (comp_left_adjoint l₁ l₂ A₁ A₂)
            (comp_left_adjoint l₁ l₂ A₁' A₂)
            _).
  cbn ; fold r₁ r₁' r₂ η₁ η₁' η₂ ε₁ ε₁' ε₂.
  etrans.
  {
    rewrite !vassocl.
    rewrite <- lwhisker_lwhisker.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite lwhisker_vcomp.
    rewrite !vassocl.
    rewrite lwhisker_lwhisker_rassociator.
    rewrite !vassocr.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite vcomp_whisker.
    rewrite !vassocr.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite lwhisker_hcomp.
      rewrite <- linvunitor_natural.
      apply idpath.
    }
    rewrite <- lwhisker_vcomp.
    rewrite vassocr.
    apply maponpaths_2.
    apply transport_unit.
  }
  rewrite <- !lwhisker_vcomp.
  rewrite !vassocl.
  apply idpath.
Qed.

Proposition rwhisker_adjoint_unique_map
            {B : bicat}
            {x y z : B}
            {l₁ : x --> y}
            {l₂ : y --> z}
            (A₁ : left_adjoint l₁)
            (A₂ A₂' : left_adjoint l₂)
            (r₁ := left_adjoint_right_adjoint A₁)
            (r₂ := left_adjoint_right_adjoint A₂)
            (r₂' := left_adjoint_right_adjoint A₂')
            (η₁ := left_adjoint_unit A₁)
            (η₂ := left_adjoint_unit A₂)
            (η₂' := left_adjoint_unit A₂')
            (ε₁ := left_adjoint_counit A₁)
            (ε₂ := left_adjoint_counit A₂)
            (ε₂' := left_adjoint_counit A₂')
  : (adjoint_unique_map _ A₂ A₂') ▹ r₁
    =
    adjoint_unique_map _ (comp_left_adjoint _ _ A₁ A₂) (comp_left_adjoint _ _ A₁ A₂').
Proof.
  refine (!_).
  refine (adjoint_unique_map_unique_cell
            (comp_left_adjoint l₁ l₂ A₁ A₂)
            (comp_left_adjoint l₁ l₂ A₁ A₂')
            _).
  cbn ; fold r₁ r₂ r₂' η₁ η₂ η₂' ε₁ ε₂ ε₂'.
  rewrite <- !lwhisker_vcomp.
  rewrite !vassocl.
  do 2 apply maponpaths.
  rewrite <- lwhisker_lwhisker.
  rewrite !vassocr.
  apply maponpaths_2.
  rewrite !lwhisker_vcomp.
  apply maponpaths.
  rewrite !vassocl.
  rewrite rwhisker_lwhisker_rassociator.
  rewrite !vassocr.
  apply maponpaths_2.
  rewrite rwhisker_vcomp.
  apply maponpaths.
  apply transport_unit.
Qed.

Proposition vcomp_adjoint_unique_map
            {B : bicat}
            {x y : B}
            {l : x --> y}
            (A₁ A₁' A₁'' : left_adjoint l)
            (r₁ := left_adjoint_right_adjoint A₁)
            (r₁' := left_adjoint_right_adjoint A₁')
            (r₁'' := left_adjoint_right_adjoint A₁'')
            (η₁ := left_adjoint_unit A₁)
            (η₁' := left_adjoint_unit A₁')
            (η₁'' := left_adjoint_unit A₁'')
            (ε₁ := left_adjoint_counit A₁)
            (ε₁' := left_adjoint_counit A₁')
            (ε₁'' := left_adjoint_counit A₁'')
  : adjoint_unique_map _ A₁ A₁' • adjoint_unique_map _ A₁' A₁''
    =
    adjoint_unique_map _ A₁ A₁''.
Proof.
  refine (!_).
  refine (adjoint_unique_map_unique_cell A₁ A₁'' _).
  cbn ; fold r₁ r₁' r₁'' η₁ η₁' η₁'' ε₁ ε₁' ε₁''.
  rewrite <- lwhisker_vcomp.
  rewrite vassocr.
  etrans.
  {
    apply maponpaths_2.
    apply transport_unit.
  }
  apply transport_unit.
Qed.      

Proposition id2_adjoint_unique_map
            {B : bicat}
            {x y : B}
            {l : x --> y}
            (A : left_adjoint l)
            (r := left_adjoint_right_adjoint A)
            (η := left_adjoint_unit A)
            (ε := left_adjoint_counit A)
  : adjoint_unique_map _ A A = id2 _.
Proof.
  use adjoint_unique_map_unique_cell.
  rewrite lwhisker_id2.
  apply id2_right.
Qed.

Proposition adjoint_unique_map_inv2cell
            {B : bicat}
            {x y : B}
            {l l' : x --> y}
            (A₁ A₂ : left_adjoint l)
            (r₁ := left_adjoint_right_adjoint A₁)
            (η₁ := left_adjoint_unit A₁)
            (ε₁ := left_adjoint_counit A₁)
            (r₂ := left_adjoint_right_adjoint A₂)
            (η₂ := left_adjoint_unit A₂)
            (ε₂ := left_adjoint_counit A₂)
            (θ : invertible_2cell l l')
  : adjoint_unique_map l A₁ A₂
    =
    adjoint_unique_map l' (left_adjoint_invertible θ A₁) (left_adjoint_invertible θ A₂).
Proof.
  use adjoint_unique_map_unique_cell.
  cbn ; fold r₁ r₂ η₁ η₂ ε₁ ε₂.
  refine (_ @ id2_right _).
  rewrite <- id2_rwhisker.
  rewrite <- (vcomp_rinv θ).
  rewrite <- rwhisker_vcomp.
  rewrite vassocr.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    exact (transport_unit _ (left_adjoint_invertible θ A₁) (left_adjoint_invertible θ A₂)).
  }
  cbn ; fold r₁ r₂ η₁ η₂ ε₁ ε₂.
  rewrite !vassocl.
  apply maponpaths.
  rewrite <- vcomp_whisker.
  rewrite !vassocr.
  rewrite rwhisker_vcomp.
  rewrite vcomp_rinv.
  rewrite id2_rwhisker.
  apply id2_left.
Qed.
