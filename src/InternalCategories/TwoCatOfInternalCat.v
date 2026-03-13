Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import InternalCategories.InternalCat.
Require Import InternalCategories.InternalFunctor.
Require Import InternalCategories.InternalNatTrans.
Require Import InternalCategories.CatOfInternalCat.

Local Open Scope cat.

(** * 1. Operations in the 2-category of internal categories *)
Definition two_cat_data_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : two_cat_data.
Proof.
  use make_two_cat_data.
  - exact (precat_data_of_internal_cat PB).
  - exact (λ d₁ d₂ f₁ f₂, internal_nat_trans f₁ f₂).
  - exact (λ d₁ d₂ f, id_internal_nat_trans f).
  - exact (λ d₁ d₂ f g h θ₁ θ₂, internal_nat_trans_comp θ₁ θ₂).
  - exact (λ d₁ d₂ d₃ f g₁ g₂ θ, internal_nat_trans_lwhisker f θ).
  - exact (λ d₁ d₂ d₃ f₁ f₂ g θ, internal_nat_trans_rwhisker θ g).
Defined.

Lemma internal_cat_idto2mor_eq
      {C : category}
      {PB : Pullbacks C}
      {d₁ d₂ : internal_cat PB}
      {f₁ f₂ : internal_functor d₁ d₂}
      (p : f₁ = f₂)
      {Γ : C}
      (x : Γ --> internal_cat_ob d₁)
  : x · internal_functor_ob f₁ = x · internal_functor_ob f₂.
Proof.
  induction p.
  apply idpath.
Qed.

Proposition internal_cat_idto2mor
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            {f₁ f₂ : internal_functor d₁ d₂}
            (p : f₁ = f₂)
            {Γ : C}
            (x : Γ --> internal_cat_ob d₁)
  : internal_nat_trans_morphism_ob
      (pr1 (idto2mor (C := two_cat_data_of_internal_cat PB) p))
      x
    =
    eq_to_internal_morphism (internal_cat_idto2mor_eq p x).
Proof.
  induction p.
  use internal_morphism_eq ; cbn.
  apply assoc.
Qed.

Definition two_cat_category_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : two_cat_category.
Proof.
  use make_two_cat_category.
  - exact (two_cat_data_of_internal_cat PB).
  - exact (pr21 (cat_of_internal_cat PB)).
  - abstract
      (intro ; intros ;
       apply isaset_internal_functor).
Defined.

#[local] Opaque id_internal_nat_trans
  internal_nat_trans_comp
  internal_nat_trans_lwhisker
  internal_nat_trans_rwhisker.

(** * 2. Laws in the 2-category of internal categories *)
Proposition two_cat_laws_of_internal_cat
            {C : category}
            (PB : Pullbacks C)
  : two_cat_laws (two_cat_category_of_internal_cat PB).
Proof.
  repeat split.
  - intros d₁ d₂ f g θ.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite comp_internal_nat_trans_ob.
    rewrite id_internal_nat_trans_ob.
    rewrite internal_morphism_id_left.
    apply idpath.
  - intros d₁ d₂ f g θ.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite comp_internal_nat_trans_ob.
    rewrite id_internal_nat_trans_ob.
    rewrite internal_morphism_id_right.
    apply idpath.
  - intros d₁ d₂ f₁ f₂ f₃ f₄ θ₁ θ₂ θ₃.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite internal_morphism_assoc.
    apply idpath.
  - intros d₁ d₂ d₃ f₁ f₂.
    use internal_nat_trans_eq'.
    cbn.
    intros Γ x.
    rewrite internal_nat_trans_lwhisker_ob.
    rewrite !id_internal_nat_trans_ob.
    rewrite internal_morphism_id_right.
    rewrite <- eq_to_internal_morphism_comp.
    rewrite eq_to_internal_morphism_id.
    apply idpath.
  - intros d₁ d₂ d₃ f₁ f₂.
    use internal_nat_trans_eq'.
    cbn.
    intros Γ x.
    rewrite internal_nat_trans_rwhisker_ob.
    rewrite !id_internal_nat_trans_ob.
    rewrite internal_functor_id.
    rewrite internal_morphism_id_right.
    rewrite <- eq_to_internal_morphism_comp.
    rewrite eq_to_internal_morphism_id.
    apply idpath.
  - intros d₁ d₂ d₃ f g₁ g₂ g₃ θ₁ θ₂.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite !internal_nat_trans_lwhisker_ob.
    rewrite comp_internal_nat_trans_ob.
    rewrite !internal_morphism_assoc'.
    apply maponpaths.
    rewrite !internal_morphism_assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      rewrite internal_morphism_assoc'.
      rewrite eq_to_internal_morphism_inv.
      apply internal_morphism_id_right.
    }
    apply idpath.
  - intros d₁ d₂ d₃ f₁ f₂ f₃ g θ₁ θ₂.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite !internal_nat_trans_rwhisker_ob.
    rewrite comp_internal_nat_trans_ob.
    rewrite !internal_morphism_assoc'.
    apply maponpaths.
    rewrite !internal_morphism_assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      rewrite internal_morphism_assoc'.
      rewrite eq_to_internal_morphism_inv.
      apply internal_morphism_id_right.
    }
    rewrite internal_functor_comp.
    apply idpath.
  - intros d₁ d₂ d₃ f₁ f₂ g₁ g₂ θ₁ θ₂.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite !internal_nat_trans_lwhisker_ob, !internal_nat_trans_rwhisker_ob.
    rewrite !internal_morphism_assoc'.
    apply maponpaths.
    rewrite !internal_morphism_assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      rewrite internal_morphism_assoc'.
      rewrite eq_to_internal_morphism_inv.
      apply internal_morphism_id_right.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      rewrite internal_morphism_assoc'.
      rewrite eq_to_internal_morphism_inv.
      apply internal_morphism_id_right.
    }
    rewrite internal_nat_trans_commutes.    
    apply idpath.
  - intros d₁ d₂ f₁ f₂ θ.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite internal_nat_trans_lwhisker_ob.
    etrans.
    {
      apply maponpaths.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    rewrite !internal_morphism_assoc'.
    rewrite <- eq_to_internal_morphism_comp.
    use internal_morphism_eq.
    rewrite !eq_to_internal_morphism_left.
    rewrite eq_to_internal_morphism_right.
    cbn.
    rewrite id_right.
    apply idpath.
  - intros d₁ d₂ f₁ f₂ θ.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite internal_nat_trans_rwhisker_ob.
    etrans.
    {
      apply maponpaths.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    rewrite !internal_morphism_assoc'.
    rewrite <- eq_to_internal_morphism_comp.
    use internal_morphism_eq.
    rewrite !eq_to_internal_morphism_left.
    rewrite eq_to_internal_morphism_right.
    cbn.
    rewrite id_right.
    apply idpath.
  - intros d₁ d₂ d₃ d₄ f₁ f₂ f₃ f₄ θ.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite !internal_nat_trans_lwhisker_ob.
    etrans.
    {
      apply maponpaths.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    rewrite !internal_morphism_assoc'.
    rewrite <- !eq_to_internal_morphism_comp.
    use internal_morphism_eq.
    rewrite !eq_to_internal_morphism_left.
    rewrite !eq_to_internal_morphism_right.
    cbn.
    rewrite !assoc'.
    apply idpath.
  - intros d₁ d₂ d₃ d₄ f₁ f₂ f₃ f₄ θ.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite internal_nat_trans_lwhisker_ob, !internal_nat_trans_rwhisker_ob.
    rewrite !internal_nat_trans_lwhisker_ob.
    etrans.
    {
      apply maponpaths.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    rewrite !internal_morphism_assoc'.
    rewrite <- !eq_to_internal_morphism_comp.
    use internal_morphism_eq.
    rewrite !eq_to_internal_morphism_left.
    rewrite !eq_to_internal_morphism_right.
    rewrite !internal_functor_comp.
    rewrite !internal_functor_eq_to_internal_morphism.
    rewrite eq_to_internal_morphism_left.
    rewrite eq_to_internal_morphism_right.
    apply idpath.
  - intros d₁ d₂ d₃ d₄ f₁ f₂ f₃ f₄ θ.
    use internal_nat_trans_eq'.
    intros Γ x.
    cbn.
    rewrite !comp_internal_nat_trans_ob.
    rewrite !internal_nat_trans_rwhisker_ob.
    etrans.
    {
      apply maponpaths_2.
      apply internal_cat_idto2mor.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply internal_cat_idto2mor.
    }
    rewrite !internal_morphism_assoc'.
    rewrite <- !eq_to_internal_morphism_comp.
    use internal_morphism_eq.
    rewrite !eq_to_internal_morphism_left.
    rewrite !eq_to_internal_morphism_right.
    rewrite comp_internal_functor_on_mor_to_mor.
    rewrite !internal_functor_comp.
    rewrite !internal_functor_eq_to_internal_morphism.
    rewrite eq_to_internal_morphism_left.
    rewrite eq_to_internal_morphism_right.
    apply idpath.
Qed.

(** * 3. The 2-category of internal categories *)
Definition two_precat_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : two_precat.
Proof.
  use make_two_precat.
  - exact (two_cat_category_of_internal_cat PB).
  - exact (two_cat_laws_of_internal_cat PB).
Defined.

Definition two_cat_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : two_cat.
Proof.
  use make_two_cat.
  - exact (two_precat_of_internal_cat PB).
  - abstract
      (intro ; intros ;
       cbn ;
       apply isaset_internal_nat_trans).
Defined.

Definition univalent_two_cat_of_internal_cat
           {C : category}
           (H : is_univalent C)
           (PB : Pullbacks C)
  : univalent_two_cat.
Proof.
  use make_univalent_two_cat.
  - exact (two_cat_of_internal_cat PB).
  - exact (is_univalent_internal_cat H PB).
Defined.
