Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
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

Section BinProductInternalCat.
  Context {C : category}
          (BP : BinProducts C)
          {PB : Pullbacks C}
          (d₁ d₂ : internal_cat PB).

  Definition binprod_internal_cat_ob
    : C
    := BP (internal_cat_ob d₁) (internal_cat_ob d₂).

  Definition binprod_internal_cat_mor
    : C
    := BP (internal_cat_mor d₁) (internal_cat_mor d₂).

  Definition binprod_internal_cat_dom
    : binprod_internal_cat_mor --> binprod_internal_cat_ob
    := BinProductOfArrows _ _ _ (internal_cat_dom d₁) (internal_cat_dom d₂).

  Definition binprod_internal_cat_cod
    : binprod_internal_cat_mor --> binprod_internal_cat_ob
    := BinProductOfArrows _ _ _ (internal_cat_cod d₁) (internal_cat_cod d₂).

  Definition binprod_internal_cat_diag
    : internal_cat_diag C.
  Proof.
    use make_internal_cat_diag.
    - exact binprod_internal_cat_ob.
    - exact binprod_internal_cat_mor.
    - exact binprod_internal_cat_dom.
    - exact binprod_internal_cat_cod.
  Defined.

  Definition binprod_internal_cat_id
    : binprod_internal_cat_ob --> binprod_internal_cat_mor
    := BinProductOfArrows _ _ _ (internal_cat_id d₁) (internal_cat_id d₂).

  Proposition binprod_internal_cat_id_dom
    : binprod_internal_cat_id · binprod_internal_cat_dom = identity _.
  Proof.
    cbn.
    unfold binprod_internal_cat_id, binprod_internal_cat_dom.
    refine (BinProductOfArrows_comp _ _ _ _ _ _ _ _ _ _ _ _ @ _).
    rewrite !internal_cat_id_dom.
    apply BinProductOfArrows_id.
  Qed.

  Proposition binprod_internal_cat_id_cod
    : binprod_internal_cat_id · binprod_internal_cat_cod = identity _.
  Proof.
    cbn.
    unfold binprod_internal_cat_id, binprod_internal_cat_dom.
    refine (BinProductOfArrows_comp _ _ _ _ _ _ _ _ _ _ _ _ @ _).
    rewrite !internal_cat_id_cod.
    apply BinProductOfArrows_id.
  Qed.

  Definition binprod_internal_cat_comp
    : PB _ _ _ binprod_internal_cat_cod binprod_internal_cat_dom
      -->
      binprod_internal_cat_mor.
  Proof.
    use BinProductArrow.
    - refine (_ · internal_cat_comp d₁).
      use PullbackArrow.
      + exact (PullbackPr1 _ · BinProductPr1 _ _).
      + exact (PullbackPr2 _ · BinProductPr1 _ _).
      + abstract
          (rewrite !assoc' ;
           rewrite <- (BinProductOfArrowsPr1
                         _ (BP _ _) (BP _ _)
                         (internal_cat_cod d₁) (internal_cat_cod d₂)) ;
           rewrite !assoc ;
           rewrite PullbackSqrCommutes ;
           rewrite !assoc' ;
           cbn ;
           apply maponpaths ;
           apply BinProductOfArrowsPr1).
    - refine (_ · internal_cat_comp d₂).
      use PullbackArrow.
      + exact (PullbackPr1 _ · BinProductPr2 _ _).
      + exact (PullbackPr2 _ · BinProductPr2 _ _).
      + abstract
          (rewrite !assoc' ;
           rewrite <- (BinProductOfArrowsPr2
                         _ (BP _ _) (BP _ _)
                         (internal_cat_cod d₁) (internal_cat_cod d₂)) ;
           rewrite !assoc ;
           rewrite PullbackSqrCommutes ;
           rewrite !assoc' ;
           cbn ;
           apply maponpaths ;
           apply BinProductOfArrowsPr2).
  Defined.

  Proposition binprod_internal_cat_comp_dom
    : binprod_internal_cat_comp · binprod_internal_cat_dom
      =
      PullbackPr1 _ · binprod_internal_cat_dom.
  Proof.
    refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _).
    rewrite !assoc'.
    rewrite !internal_cat_comp_dom.
    rewrite !assoc.
    rewrite !PullbackArrow_PullbackPr1.
    refine (!_).
    use BinProductArrowUnique.
    - rewrite !assoc'.
      apply maponpaths.
      apply BinProductOfArrowsPr1.
    - rewrite !assoc'.
      apply maponpaths.
      apply BinProductOfArrowsPr2.
  Qed.

  Proposition binprod_internal_cat_comp_cod
    : binprod_internal_cat_comp · binprod_internal_cat_cod
      =
      PullbackPr2 _ · binprod_internal_cat_cod.
  Proof.
    refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _).
    rewrite !assoc'.
    rewrite !internal_cat_comp_cod.
    rewrite !assoc.
    rewrite !PullbackArrow_PullbackPr2.
    refine (!_).
    use BinProductArrowUnique.
    - rewrite !assoc'.
      apply maponpaths.
      apply BinProductOfArrowsPr1.
    - rewrite !assoc'.
      apply maponpaths.
      apply BinProductOfArrowsPr2.
  Qed.

  Definition binprod_internal_cat_id_comp
    : internal_cat_id_comp PB binprod_internal_cat_diag.
  Proof.
    split.
    - simple refine (_ ,, _ ,, _).
      + exact binprod_internal_cat_id.
      + exact binprod_internal_cat_id_dom.
      + exact binprod_internal_cat_id_cod.
    - simple refine (_ ,, _ ,, _).
      + exact binprod_internal_cat_comp.
      + exact binprod_internal_cat_comp_dom.
      + exact binprod_internal_cat_comp_cod.
  Defined.
  
  Definition binprod_internal_cat_data
    : internal_cat_data PB.
  Proof.
    use make_internal_cat_data.
    - exact binprod_internal_cat_diag.
    - exact binprod_internal_cat_id_comp.
  Defined.

  Definition binprod_internal_ob_pr1
             {Γ : C}
             (x : Γ --> binprod_internal_cat_ob)
    : Γ --> internal_cat_ob d₁
    := x · BinProductPr1 _ _.

  Definition binprod_internal_ob_pr2
             {Γ : C}
             (x : Γ --> binprod_internal_cat_ob)
    : Γ --> internal_cat_ob d₂
    := x · BinProductPr2 _ _.

  Definition binprod_internal_mor_pr1
             {Γ : C}
             {x y : Γ --> binprod_internal_cat_ob}
             (f : internal_morphism (d := binprod_internal_cat_diag) x y)
    : internal_morphism (binprod_internal_ob_pr1 x) (binprod_internal_ob_pr1 y).
  Proof.
    use make_internal_morphism.
    - exact (f · BinProductPr1 _ _).
    - abstract
        (refine (_ @ maponpaths (λ z, z · BinProductPr1 _ _) (internal_morphism_dom f)) ;
         rewrite !assoc' ;
         apply maponpaths ;
         refine (!_) ;
         apply BinProductOfArrowsPr1).
    - abstract
        (refine (_ @ maponpaths (λ z, z · BinProductPr1 _ _) (internal_morphism_cod f)) ;
         rewrite !assoc' ;
         apply maponpaths ;
         refine (!_) ;
         apply BinProductOfArrowsPr1).
  Defined.

  Definition binprod_internal_mor_pr2
             {Γ : C}
             {x y : Γ --> binprod_internal_cat_ob}
             (f : internal_morphism (d := binprod_internal_cat_diag) x y)
    : internal_morphism (binprod_internal_ob_pr2 x) (binprod_internal_ob_pr2 y).
  Proof.
    use make_internal_morphism.
    - exact (f · BinProductPr2 _ _).
    - abstract
        (refine (_ @ maponpaths (λ z, z · BinProductPr2 _ _) (internal_morphism_dom f)) ;
         rewrite !assoc' ;
         apply maponpaths ;
         refine (!_) ;
         apply BinProductOfArrowsPr2).
    - abstract
        (refine (_ @ maponpaths (λ z, z · BinProductPr2 _ _) (internal_morphism_cod f)) ;
         rewrite !assoc' ;
         apply maponpaths ;
         refine (!_) ;
         apply BinProductOfArrowsPr2).
  Defined.

  Proposition binprod_internal_mor_eq
              {Γ : C}
              {x y : Γ --> binprod_internal_cat_ob}
              {f g : internal_morphism (d := binprod_internal_cat_diag) x y}
              (p : binprod_internal_mor_pr1 f = binprod_internal_mor_pr1 g)
              (q : binprod_internal_mor_pr2 f = binprod_internal_mor_pr2 g)
    : f = g.
  Proof.
    use internal_morphism_eq.
    use BinProductArrowsEq.
    - exact (maponpaths pr1 p).
    - exact (maponpaths pr1 q).
  Qed.

  Proposition binprod_internal_cat_id_pr1
              {Γ : C}
              (x : Γ --> internal_cat_ob binprod_internal_cat_data)
    : binprod_internal_mor_pr1 (idi x) = idi _.
  Proof.
    use internal_morphism_eq ; cbn.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    apply BinProductOfArrowsPr1.
  Qed.

  Proposition binprod_internal_cat_id_pr2
              {Γ : C}
              (x : Γ --> internal_cat_ob binprod_internal_cat_data)
    : binprod_internal_mor_pr2 (idi x) = idi _.
  Proof.
    use internal_morphism_eq ; cbn.
    refine (assoc' _ _ _ @ _ @ assoc _ _ _).
    apply maponpaths.
    apply BinProductOfArrowsPr2.
  Qed.

  Proposition binprod_internal_cat_comp_pr1
              {Γ : C}
              {x y z : Γ --> internal_cat_ob binprod_internal_cat_data}
              (f : internal_morphism x y)
              (g : internal_morphism y z)
    : binprod_internal_mor_pr1 (f ·i g)
      =
      binprod_internal_mor_pr1 f ·i binprod_internal_mor_pr1 g.
  Proof.
    use internal_morphism_eq ; cbn.
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      apply BinProductPr1Commutes.
    }
    rewrite !assoc.
    apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr1.
      rewrite assoc.
      rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr2.
      rewrite assoc.
      rewrite PullbackArrow_PullbackPr2.
      apply idpath.
  Qed.

  Proposition binprod_internal_cat_comp_pr2
              {Γ : C}
              {x y z : Γ --> internal_cat_ob binprod_internal_cat_data}
              (f : internal_morphism x y)
              (g : internal_morphism y z)
    : binprod_internal_mor_pr2 (f ·i g)
      =
      binprod_internal_mor_pr2 f ·i binprod_internal_mor_pr2 g.
  Proof.
    use internal_morphism_eq ; cbn.
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      apply BinProductPr2Commutes.
    }
    rewrite !assoc.
    apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr1.
      rewrite assoc.
      rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr2.
      rewrite assoc.
      rewrite PullbackArrow_PullbackPr2.
      apply idpath.
  Qed.
    
  Proposition binprod_internal_cat_laws
    : disp_cat_axioms C (internal_cat_disp_cat_data binprod_internal_cat_data).
  Proof.
    use make_internal_cat_axioms.
    - intros.
      use binprod_internal_mor_eq.
      + rewrite binprod_internal_cat_comp_pr1.
        rewrite binprod_internal_cat_id_pr1.
        apply internal_morphism_id_left.
      + rewrite binprod_internal_cat_comp_pr2.
        rewrite binprod_internal_cat_id_pr2.
        apply internal_morphism_id_left.
    - intros.
      use binprod_internal_mor_eq.
      + rewrite binprod_internal_cat_comp_pr1.
        rewrite binprod_internal_cat_id_pr1.
        apply internal_morphism_id_right.
      + rewrite binprod_internal_cat_comp_pr2.
        rewrite binprod_internal_cat_id_pr2.
        apply internal_morphism_id_right.
    - intros.
      use binprod_internal_mor_eq.
      + rewrite !binprod_internal_cat_comp_pr1.
        apply internal_morphism_assoc.
      + rewrite !binprod_internal_cat_comp_pr2.
        apply internal_morphism_assoc.
  Qed.
  
  Definition binprod_internal_cat
    : internal_cat PB.
  Proof.
    use make_internal_cat.
    - exact binprod_internal_cat_data.
    - exact binprod_internal_cat_laws.
  Defined.

  Definition binprod_internal_cat_pr1_data
    : internal_functor_data binprod_internal_cat d₁.
  Proof.
    use make_internal_functor_data.
    - split.
      + exact (BinProductPr1 _ _).
      + exact (BinProductPr1 _ _).
    - abstract
        (cbn ;
         refine (!_) ;
         apply BinProductOfArrowsPr1).
    - abstract
        (cbn ;
         refine (!_) ;
         apply BinProductOfArrowsPr1).
  Defined.

  Proposition binprod_internal_cat_pr1_axioms
    : disp_functor_axioms
        (internal_functor_to_disp_functor_data
           binprod_internal_cat_pr1_data).
  Proof.
    use make_internal_functor_axioms.
    - intros Γ x.
      use internal_morphism_eq ; cbn.
      rewrite !assoc'.
      apply maponpaths.
      apply BinProductOfArrowsPr1.
    - intros Γ x₁ x₂ x₃ g₁ g₂.
      use internal_morphism_eq ; cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply BinProductPr1Commutes.
      }
      rewrite !assoc.
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
  Qed.

  Definition binprod_internal_cat_pr1
    : internal_functor binprod_internal_cat d₁.
  Proof.
    use make_internal_functor.
    - exact binprod_internal_cat_pr1_data.
    - exact binprod_internal_cat_pr1_axioms.
  Defined.

  Proposition binprod_internal_cat_pr1_on_mor
              {Γ : C}
              {x y : Γ --> binprod_internal_cat_ob}
              (f : internal_morphism (d := binprod_internal_cat_diag) x y)
    : internal_functor_on_mor binprod_internal_cat_pr1 f
      =
      binprod_internal_mor_pr1 f.
  Proof.
    use internal_morphism_eq ; cbn.
    apply idpath.
  Qed.

  Definition binprod_internal_cat_pr2_data
    : internal_functor_data binprod_internal_cat d₂.
  Proof.
    use make_internal_functor_data.
    - split.
      + exact (BinProductPr2 _ _).
      + exact (BinProductPr2 _ _).
    - abstract
        (cbn ;
         refine (!_) ;
         apply BinProductOfArrowsPr2).
    - abstract
        (cbn ;
         refine (!_) ;
         apply BinProductOfArrowsPr2).
  Defined.

  Proposition binprod_internal_cat_pr2_axioms
    : disp_functor_axioms
        (internal_functor_to_disp_functor_data
           binprod_internal_cat_pr2_data).
  Proof.
    use make_internal_functor_axioms.
    - intros Γ x.
      use internal_morphism_eq ; cbn.
      rewrite !assoc'.
      apply maponpaths.
      apply BinProductOfArrowsPr2.
    - intros Γ x₁ x₂ x₃ g₁ g₂.
      use internal_morphism_eq ; cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply BinProductPr2Commutes.
      }
      rewrite !assoc.
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite !assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
  Qed.

  Definition binprod_internal_cat_pr2
    : internal_functor binprod_internal_cat d₂.
  Proof.
    use make_internal_functor.
    - exact binprod_internal_cat_pr2_data.
    - exact binprod_internal_cat_pr2_axioms.
  Defined.

  Proposition binprod_internal_cat_pr2_on_mor
              {Γ : C}
              {x y : Γ --> binprod_internal_cat_ob}
              (f : internal_morphism (d := binprod_internal_cat_diag) x y)
    : internal_functor_on_mor binprod_internal_cat_pr2 f
      =
      binprod_internal_mor_pr2 f.
  Proof.
    use internal_morphism_eq ; cbn.
    apply idpath.
  Qed.

  Definition binprod_internal_cat_pair_data
             {c : internal_cat PB}
             (f₁ : internal_functor c d₁)
             (f₂ : internal_functor c d₂)
    : internal_functor_data c binprod_internal_cat.
  Proof.
    use make_internal_functor_data.
    - split.
      + exact (BinProductArrow _ _ (internal_functor_ob f₁) (internal_functor_ob f₂)).
      + exact (BinProductArrow _ _ (internal_functor_mor f₁) (internal_functor_mor f₂)).
    - abstract
        (cbn ;
         unfold binprod_internal_cat_dom ;
         refine (_ @ !(precompWithBinProductArrow _ _ _ _ _)) ;
         refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _) ;
         rewrite !internal_functor_mor_dom ;
         apply idpath).
    - abstract
        (cbn ;
         unfold binprod_internal_cat_dom ;
         refine (_ @ !(precompWithBinProductArrow _ _ _ _ _)) ;
         refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _) ;
         rewrite !internal_functor_mor_cod ;
         apply idpath).
  Defined.

  Proposition binprod_internal_cat_pair_data_ob_pr1
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
              {Γ : C}
              (x : Γ --> internal_cat_ob c)
    : binprod_internal_ob_pr1 (x · internal_functor_ob (binprod_internal_cat_pair_data f₁ f₂))
      =
      x · internal_functor_ob f₁.
  Proof.
    unfold binprod_internal_ob_pr1 ; cbn.
    rewrite !assoc'.
    apply maponpaths.
    apply BinProductPr1Commutes.
  Qed.
    
  Proposition binprod_internal_cat_pair_data_mor_pr1
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
              {Γ : C}
              {x y : Γ --> internal_cat_ob c}
              (g : internal_morphism x y)
    : binprod_internal_mor_pr1
        (internal_functor_on_mor (binprod_internal_cat_pair_data f₁ f₂) g)
      =
      eq_to_internal_morphism (binprod_internal_cat_pair_data_ob_pr1 f₁ f₂ x)
      ·i internal_functor_on_mor f₁ g
      ·i eq_to_internal_morphism (!(binprod_internal_cat_pair_data_ob_pr1 f₁ f₂ y)).
  Proof.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_right.
    rewrite eq_to_internal_morphism_left.
    cbn.
    rewrite !assoc'.
    apply maponpaths.
    apply BinProductPr1Commutes.
  Qed.

  Proposition binprod_internal_cat_pair_data_ob_pr2
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
              {Γ : C}
              (x : Γ --> internal_cat_ob c)
    : binprod_internal_ob_pr2 (x · internal_functor_ob (binprod_internal_cat_pair_data f₁ f₂))
      =
      x · internal_functor_ob f₂.
  Proof.
    unfold binprod_internal_ob_pr2 ; cbn.
    rewrite !assoc'.
    apply maponpaths.
    apply BinProductPr2Commutes.
  Qed.
    
  Proposition binprod_internal_cat_pair_data_mor_pr2
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
              {Γ : C}
              {x y : Γ --> internal_cat_ob c}
              (g : internal_morphism x y)
    : binprod_internal_mor_pr2
        (internal_functor_on_mor (binprod_internal_cat_pair_data f₁ f₂) g)
      =
      eq_to_internal_morphism (binprod_internal_cat_pair_data_ob_pr2 f₁ f₂ x)
      ·i internal_functor_on_mor f₂ g
      ·i eq_to_internal_morphism (!(binprod_internal_cat_pair_data_ob_pr2 f₁ f₂ y)).
  Proof.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_right.
    rewrite eq_to_internal_morphism_left.
    cbn.
    rewrite !assoc'.
    apply maponpaths.
    apply BinProductPr2Commutes.
  Qed.

  Proposition binprod_internal_cat_pair_laws
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
    : disp_functor_axioms
        (internal_functor_to_disp_functor_data
           (binprod_internal_cat_pair_data f₁ f₂)).
  Proof.
    use make_internal_functor_axioms.
    - intros Γ x.
      use binprod_internal_mor_eq.
      + rewrite binprod_internal_cat_id_pr1.
        rewrite binprod_internal_cat_pair_data_mor_pr1.
        rewrite internal_functor_id.
        use internal_morphism_eq.
        rewrite eq_to_internal_morphism_right.
        rewrite eq_to_internal_morphism_left.
        rewrite binprod_internal_cat_pair_data_ob_pr1.
        apply idpath.
      + rewrite binprod_internal_cat_id_pr2.
        rewrite binprod_internal_cat_pair_data_mor_pr2.
        rewrite internal_functor_id.
        use internal_morphism_eq.
        rewrite eq_to_internal_morphism_right.
        rewrite eq_to_internal_morphism_left.
        rewrite binprod_internal_cat_pair_data_ob_pr2.
        apply idpath.
    - intros Γ x₁ x₂ x₃ g₁ g₂.
      use binprod_internal_mor_eq.
      + rewrite binprod_internal_cat_comp_pr1.
        rewrite !binprod_internal_cat_pair_data_mor_pr1.
        rewrite internal_functor_comp.
        rewrite !internal_morphism_assoc.
        use internal_morphism_eq.
        rewrite !eq_to_internal_morphism_right.
        rewrite !internal_morphism_assoc'.
        rewrite !eq_to_internal_morphism_left.
        do 2 apply maponpaths.
        use internal_morphism_eq.
        rewrite !eq_to_internal_morphism_left.
        apply idpath.
      + rewrite binprod_internal_cat_comp_pr2.
        rewrite !binprod_internal_cat_pair_data_mor_pr2.
        rewrite internal_functor_comp.
        rewrite !internal_morphism_assoc.
        use internal_morphism_eq.
        rewrite !eq_to_internal_morphism_right.
        rewrite !internal_morphism_assoc'.
        rewrite !eq_to_internal_morphism_left.
        do 2 apply maponpaths.
        use internal_morphism_eq.
        rewrite !eq_to_internal_morphism_left.
        apply idpath.
  Qed.
  
  Definition binprod_internal_cat_pair
             {c : internal_cat PB}
             (f₁ : internal_functor c d₁)
             (f₂ : internal_functor c d₂)
    : internal_functor c binprod_internal_cat.
  Proof.
    use make_internal_functor.
    - exact (binprod_internal_cat_pair_data f₁ f₂).
    - exact (binprod_internal_cat_pair_laws f₁ f₂).
  Defined.

  Proposition binprod_internal_cat_pair_mor_pr1
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
              {Γ : C}
              {x y : Γ --> internal_cat_ob c}
              (g : internal_morphism x y)
    : binprod_internal_mor_pr1
        (internal_functor_on_mor (binprod_internal_cat_pair f₁ f₂) g)
      =
      eq_to_internal_morphism (binprod_internal_cat_pair_data_ob_pr1 f₁ f₂ x)
      ·i internal_functor_on_mor f₁ g
      ·i eq_to_internal_morphism (!(binprod_internal_cat_pair_data_ob_pr1 f₁ f₂ y)).
  Proof.
    apply binprod_internal_cat_pair_data_mor_pr1.
  Qed.
    
  Proposition binprod_internal_cat_pair_mor_pr2
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
              {Γ : C}
              {x y : Γ --> internal_cat_ob c}
              (g : internal_morphism x y)
    : binprod_internal_mor_pr2
        (internal_functor_on_mor (binprod_internal_cat_pair f₁ f₂) g)
      =
      eq_to_internal_morphism (binprod_internal_cat_pair_data_ob_pr2 f₁ f₂ x)
      ·i internal_functor_on_mor f₂ g
      ·i eq_to_internal_morphism (!(binprod_internal_cat_pair_data_ob_pr2 f₁ f₂ y)).
  Proof.
    apply binprod_internal_cat_pair_data_mor_pr2.
  Qed.

  Proposition binprod_internal_cat_pair_pr1
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
    : comp_internal_functor
        (binprod_internal_cat_pair f₁ f₂)
        binprod_internal_cat_pr1
      =
      f₁.
  Proof.
    use internal_functor_eq ; cbn.
    - apply BinProductPr1Commutes.
    - apply BinProductPr1Commutes.
  Qed.

  Proposition binprod_internal_cat_pair_pr2
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
    : comp_internal_functor
        (binprod_internal_cat_pair f₁ f₂)
        binprod_internal_cat_pr2
      =
      f₂.
  Proof.
    use internal_functor_eq ; cbn.
    - apply BinProductPr2Commutes.
    - apply BinProductPr2Commutes.
  Qed.

  Proposition binprod_internal_cat_pair_unique
              {c : internal_cat PB}
              (f₁ : internal_functor c d₁)
              (f₂ : internal_functor c d₂)
              (fg : internal_functor c binprod_internal_cat)
              (p₁ : comp_internal_functor fg binprod_internal_cat_pr1 = f₁)
              (p₂ : comp_internal_functor fg binprod_internal_cat_pr2 = f₂)
    : fg = binprod_internal_cat_pair f₁ f₂.
  Proof.
    use internal_functor_eq.
    - use BinProductArrowUnique.
      + exact (maponpaths (λ z, pr111 z) p₁).
      + exact (maponpaths (λ z, pr111 z) p₂).
    - use BinProductArrowUnique.
      + exact (maponpaths (λ z, dirprod_pr2 (pr11 z)) p₁).
      + exact (maponpaths (λ z, dirprod_pr2 (pr11 z)) p₂).
  Qed.

  Definition binprod_internal_cat_nat_trans_data
             {c : internal_cat PB}
             {f₁ f₂ : internal_functor c binprod_internal_cat}
             (θ₁ : internal_nat_trans
                     (comp_internal_functor f₁ binprod_internal_cat_pr1)
                     (comp_internal_functor f₂ binprod_internal_cat_pr1))
             (θ₂ : internal_nat_trans
                     (comp_internal_functor f₁ binprod_internal_cat_pr2)
                     (comp_internal_functor f₂ binprod_internal_cat_pr2))
    : internal_nat_trans_data f₁ f₂.
  Proof.
    use make_internal_nat_trans_data.
    - use BinProductArrow.
      + exact (internal_nat_trans_mor θ₁).
      + exact (internal_nat_trans_mor θ₂).
    - abstract
        (refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _) ;
         rewrite !internal_nat_trans_dom ;
         refine (!_) ;
         apply BinProductArrowEta).
    - abstract
        (refine (postcompWithBinProductArrow _ _ _ _ _ _ _ @ _) ;
         rewrite !internal_nat_trans_cod ;
         refine (!_) ;
         apply BinProductArrowEta).
  Defined.

  Proposition binprod_internal_cat_nat_trans_data_pr1
              {c : internal_cat PB}
              {f₁ f₂ : internal_functor c binprod_internal_cat}
              (θ₁ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr1)
                      (comp_internal_functor f₂ binprod_internal_cat_pr1))
              (θ₂ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr2)
                      (comp_internal_functor f₂ binprod_internal_cat_pr2))
              {Γ : C}
              (x : Γ --> internal_cat_ob c)
    : binprod_internal_mor_pr1
        (internal_nat_trans_morphism_ob
           (binprod_internal_cat_nat_trans_data θ₁ θ₂)
           x)
      =
      eq_to_internal_morphism (assoc' _ _ _)
      ·i internal_nat_trans_morphism_ob θ₁ x
      ·i eq_to_internal_morphism (assoc _ _ _).
  Proof.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_right.
    rewrite eq_to_internal_morphism_left.
    cbn.
    rewrite assoc'.
    apply maponpaths.
    apply BinProductPr1Commutes.
  Qed.

  Proposition binprod_internal_cat_nat_trans_data_pr2
              {c : internal_cat PB}
              {f₁ f₂ : internal_functor c binprod_internal_cat}
              (θ₁ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr1)
                      (comp_internal_functor f₂ binprod_internal_cat_pr1))
              (θ₂ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr2)
                      (comp_internal_functor f₂ binprod_internal_cat_pr2))
              {Γ : C}
              (x : Γ --> internal_cat_ob c)
    : binprod_internal_mor_pr2
        (internal_nat_trans_morphism_ob
           (binprod_internal_cat_nat_trans_data θ₁ θ₂)
           x)
      =
      eq_to_internal_morphism (assoc' _ _ _)
      ·i internal_nat_trans_morphism_ob θ₂ x
      ·i eq_to_internal_morphism (assoc _ _ _).
  Proof.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_right.
    rewrite eq_to_internal_morphism_left.
    cbn.
    rewrite assoc'.
    apply maponpaths.
    apply BinProductPr2Commutes.
  Qed.

  Proposition binprod_internal_cat_nat_trans_laws
              {c : internal_cat PB}
              {f₁ f₂ : internal_functor c binprod_internal_cat}
              (θ₁ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr1)
                      (comp_internal_functor f₂ binprod_internal_cat_pr1))
              (θ₂ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr2)
                      (comp_internal_functor f₂ binprod_internal_cat_pr2))
    : disp_nat_trans_axioms
        (internal_nat_trans_data_to_disp_nat_trans
           (binprod_internal_cat_nat_trans_data θ₁ θ₂)).
  Proof.
    use make_internal_nat_trans_laws.
    intros Γ x₁ x₂ g.
    use binprod_internal_mor_eq.
    - rewrite !binprod_internal_cat_comp_pr1.
      rewrite !binprod_internal_cat_nat_trans_data_pr1.
      rewrite !internal_morphism_assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        rewrite <- binprod_internal_cat_pr1_on_mor.
        exact (comp_internal_functor_on_mor' f₁ binprod_internal_cat_pr1 g).
      }
      etrans.
      {
        apply maponpaths_2.
        rewrite !internal_morphism_assoc'.
        apply maponpaths.
        exact (internal_nat_trans_commutes θ₁ g).
      }
      rewrite !internal_morphism_assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (comp_internal_functor_on_mor f₂ binprod_internal_cat_pr1 g).
      }
      rewrite binprod_internal_cat_pr1_on_mor.
      apply idpath.
    - rewrite !binprod_internal_cat_comp_pr2.
      rewrite !binprod_internal_cat_nat_trans_data_pr2.
      rewrite !internal_morphism_assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        rewrite <- binprod_internal_cat_pr2_on_mor.
        exact (comp_internal_functor_on_mor' f₁ binprod_internal_cat_pr2 g).
      }
      etrans.
      {
        apply maponpaths_2.
        rewrite !internal_morphism_assoc'.
        apply maponpaths.
        exact (internal_nat_trans_commutes θ₂ g).
      }
      rewrite !internal_morphism_assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (comp_internal_functor_on_mor f₂ binprod_internal_cat_pr2 g).
      }
      rewrite binprod_internal_cat_pr2_on_mor.
      apply idpath.
  Qed.
      
  Definition binprod_internal_cat_nat_trans
             {c : internal_cat PB}
             {f₁ f₂ : internal_functor c binprod_internal_cat}
             (θ₁ : internal_nat_trans
                     (comp_internal_functor f₁ binprod_internal_cat_pr1)
                     (comp_internal_functor f₂ binprod_internal_cat_pr1))
             (θ₂ : internal_nat_trans
                     (comp_internal_functor f₁ binprod_internal_cat_pr2)
                     (comp_internal_functor f₂ binprod_internal_cat_pr2))
    : internal_nat_trans f₁ f₂.
  Proof.
    use make_internal_nat_trans.
    - exact (binprod_internal_cat_nat_trans_data θ₁ θ₂).
    - exact (binprod_internal_cat_nat_trans_laws θ₁ θ₂).
  Defined.

  Proposition binprod_internal_cat_nat_trans_mor_pr1
              {c : internal_cat PB}
              {f₁ f₂ : internal_functor c binprod_internal_cat}
              (θ₁ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr1)
                      (comp_internal_functor f₂ binprod_internal_cat_pr1))
              (θ₂ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr2)
                      (comp_internal_functor f₂ binprod_internal_cat_pr2))
              {Γ : C}
              (x : Γ --> internal_cat_ob c)
    : binprod_internal_mor_pr1
        (internal_nat_trans_morphism_ob
           (binprod_internal_cat_nat_trans θ₁ θ₂)
           x)
      =
      eq_to_internal_morphism (assoc' _ _ _)
      ·i internal_nat_trans_morphism_ob θ₁ x
      ·i eq_to_internal_morphism (assoc _ _ _).
  Proof.
    apply binprod_internal_cat_nat_trans_data_pr1.
  Qed.

  Proposition binprod_internal_cat_nat_trans_mor_pr2
              {c : internal_cat PB}
              {f₁ f₂ : internal_functor c binprod_internal_cat}
              (θ₁ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr1)
                      (comp_internal_functor f₂ binprod_internal_cat_pr1))
              (θ₂ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr2)
                      (comp_internal_functor f₂ binprod_internal_cat_pr2))
              {Γ : C}
              (x : Γ --> internal_cat_ob c)
    : binprod_internal_mor_pr2
        (internal_nat_trans_morphism_ob
           (binprod_internal_cat_nat_trans θ₁ θ₂)
           x)
      =
      eq_to_internal_morphism (assoc' _ _ _)
      ·i internal_nat_trans_morphism_ob θ₂ x
      ·i eq_to_internal_morphism (assoc _ _ _).
  Proof.
    apply binprod_internal_cat_nat_trans_data_pr2.
  Qed.

  Proposition binprod_internal_cat_nat_trans_pr1
              {c : internal_cat PB}
              {f₁ f₂ : internal_functor c binprod_internal_cat}
              (θ₁ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr1)
                      (comp_internal_functor f₂ binprod_internal_cat_pr1))
              (θ₂ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr2)
                      (comp_internal_functor f₂ binprod_internal_cat_pr2))
    : internal_nat_trans_rwhisker
        (binprod_internal_cat_nat_trans θ₁ θ₂)
        binprod_internal_cat_pr1
      =
      θ₁.
  Proof.
    use internal_nat_trans_eq'.
    intros Γ x.
    rewrite internal_nat_trans_rwhisker_ob.
    rewrite binprod_internal_cat_pr1_on_mor.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_right.
    rewrite eq_to_internal_morphism_left.
    cbn.
    rewrite !assoc'.
    apply maponpaths.
    apply BinProductPr1Commutes.
  Qed.

  Proposition binprod_internal_cat_nat_trans_pr2
              {c : internal_cat PB}
              {f₁ f₂ : internal_functor c binprod_internal_cat}
              (θ₁ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr1)
                      (comp_internal_functor f₂ binprod_internal_cat_pr1))
              (θ₂ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr2)
                      (comp_internal_functor f₂ binprod_internal_cat_pr2))
    : internal_nat_trans_rwhisker
        (binprod_internal_cat_nat_trans θ₁ θ₂)
        binprod_internal_cat_pr2
      =
      θ₂.
  Proof.
    use internal_nat_trans_eq'.
    intros Γ x.
    rewrite internal_nat_trans_rwhisker_ob.
    rewrite binprod_internal_cat_pr2_on_mor.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_right.
    rewrite eq_to_internal_morphism_left.
    cbn.
    rewrite !assoc'.
    apply maponpaths.
    apply BinProductPr2Commutes.
  Qed.

  Proposition binprod_internal_cat_nat_trans_unique
              {c : internal_cat PB}
              {f₁ f₂ : internal_functor c binprod_internal_cat}
              (θ₁ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr1)
                      (comp_internal_functor f₂ binprod_internal_cat_pr1))
              (θ₂ : internal_nat_trans
                      (comp_internal_functor f₁ binprod_internal_cat_pr2)
                      (comp_internal_functor f₂ binprod_internal_cat_pr2))
              {τ : internal_nat_trans f₁ f₂}
              (p₁ : internal_nat_trans_rwhisker τ binprod_internal_cat_pr1 = θ₁)
              (p₂ : internal_nat_trans_rwhisker τ binprod_internal_cat_pr2 = θ₂)
    : τ = binprod_internal_cat_nat_trans θ₁ θ₂.
  Proof.
    use internal_nat_trans_eq'.
    intros Γ x.
    use binprod_internal_mor_eq.
    - rewrite binprod_internal_cat_nat_trans_mor_pr1.
      use internal_morphism_eq.
      rewrite eq_to_internal_morphism_right.
      rewrite eq_to_internal_morphism_left.
      cbn.
      rewrite !assoc'.
      apply maponpaths.
      exact (maponpaths (λ z, pr11 z) p₁).
    - rewrite binprod_internal_cat_nat_trans_mor_pr2.
      use internal_morphism_eq.
      rewrite eq_to_internal_morphism_right.
      rewrite eq_to_internal_morphism_left.
      cbn.
      rewrite !assoc'.
      apply maponpaths.
      exact (maponpaths (λ z, pr11 z) p₂).
  Qed.
End BinProductInternalCat.

Definition binproducts_cat_of_internal_cat
           {C : category}
           (BP : BinProducts C)
           (PB : Pullbacks C)
  : BinProducts (cat_of_internal_cat PB).
Proof.
  intros d₁ d₂.
  use make_BinProduct.
  - exact (binprod_internal_cat BP d₁ d₂).
  - exact (binprod_internal_cat_pr1 BP d₁ d₂).
  - exact (binprod_internal_cat_pr2 BP d₁ d₂).
  - intros c f₁ f₂.
    use make_iscontr.
    + simple refine (_ ,, _ ,, _).
      * exact (binprod_internal_cat_pair BP d₁ d₂ f₁ f₂).
      * exact (binprod_internal_cat_pair_pr1 BP d₁ d₂ f₁ f₂).
      * exact (binprod_internal_cat_pair_pr2 BP d₁ d₂ f₁ f₂).
    + abstract
        (intros (fg & p₁ & p₂) ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         exact (binprod_internal_cat_pair_unique BP d₁ d₂ f₁ f₂ fg p₁ p₂)).
Defined.
