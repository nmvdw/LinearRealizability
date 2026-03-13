Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import InternalCategories.InternalCat.
Require Import InternalCategories.InternalFunctor.

Local Open Scope cat.

(** * 1. Internal natural transformations *)
Definition internal_nat_trans_data
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           (f₁ f₂ : internal_functor d₁ d₂)
  : UU
  := ∑ (θ : internal_cat_ob d₁ --> internal_cat_mor d₂),
     (θ · internal_cat_dom d₂ = internal_functor_ob f₁)
     ×
     (θ · internal_cat_cod d₂ = internal_functor_ob f₂).

Definition make_internal_nat_trans_data
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           {f₁ f₂ : internal_functor d₁ d₂}
           (θ : internal_cat_ob d₁ --> internal_cat_mor d₂)
           (p : θ · internal_cat_dom d₂ = internal_functor_ob f₁)
           (q : θ · internal_cat_cod d₂ = internal_functor_ob f₂)
  : internal_nat_trans_data f₁ f₂
  := θ ,, p ,, q.

Coercion internal_nat_trans_mor
         {C : category}
         {PB : Pullbacks C}
         {d₁ d₂ : internal_cat PB}
         {f₁ f₂ : internal_functor d₁ d₂}
         (θ : internal_nat_trans_data f₁ f₂)
  : internal_cat_ob d₁ --> internal_cat_mor d₂
  := pr1 θ.

Definition internal_nat_trans_dom
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           {f₁ f₂ : internal_functor d₁ d₂}
           (θ : internal_nat_trans_data f₁ f₂)
  : θ · internal_cat_dom d₂ = internal_functor_ob f₁
  := pr12 θ.

Definition internal_nat_trans_cod
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           {f₁ f₂ : internal_functor d₁ d₂}
           (θ : internal_nat_trans_data f₁ f₂)
  : θ · internal_cat_cod d₂ = internal_functor_ob f₂
  := pr22 θ.

Definition internal_nat_trans_morphism
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           {f₁ f₂ : internal_functor d₁ d₂}
           (θ : internal_nat_trans_data f₁ f₂)
  : internal_morphism (internal_functor_ob f₁) (internal_functor_ob f₂).
Proof.
  use make_internal_morphism.
  - exact θ.
  - apply internal_nat_trans_dom.
  - apply internal_nat_trans_cod.
Defined.

Definition internal_nat_trans_morphism_ob
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           {f₁ f₂ : internal_functor d₁ d₂}
           (θ : internal_nat_trans_data f₁ f₂)
           {Γ : C}
           (x : Γ --> internal_cat_ob d₁)
  : internal_morphism
      (x · internal_functor_ob f₁)
      (x · internal_functor_ob f₂).
Proof.
  use make_internal_morphism.
  - exact (x · θ).
  - abstract
      (rewrite !assoc' ;
       rewrite internal_nat_trans_dom ;
       apply idpath).
  - abstract
      (rewrite assoc' ;
       rewrite internal_nat_trans_cod ;
       apply idpath).
Defined.
           
Definition internal_nat_trans_data_to_disp_nat_trans
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           {f₁ f₂ : internal_functor d₁ d₂}
           (θ : internal_nat_trans_data f₁ f₂)
  : disp_nat_trans_data
      (nat_trans_id _)
      (internal_functor_to_disp_functor f₁)
      (internal_functor_to_disp_functor f₂).
Proof.
  intros Γ x.
  use make_internal_morphism.
  - exact (x · θ).
  - abstract
      (cbn ;
       rewrite !assoc' ;
       rewrite internal_nat_trans_dom ;
       apply idpath).
  - abstract
      (cbn ;
       rewrite !assoc' ;
       rewrite internal_nat_trans_cod ;
       apply idpath).
Defined.

Definition internal_nat_trans
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           (f₁ f₂ : internal_functor d₁ d₂)
  : UU
  := ∑ (θ : internal_nat_trans_data f₁ f₂),
     disp_nat_trans_axioms (internal_nat_trans_data_to_disp_nat_trans θ).

Definition make_internal_nat_trans
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           {f₁ f₂ : internal_functor d₁ d₂}
           (θ : internal_nat_trans_data f₁ f₂)
           (p : disp_nat_trans_axioms (internal_nat_trans_data_to_disp_nat_trans θ))
  : internal_nat_trans f₁ f₂
  := θ ,, p.

Coercion internal_nat_trans_to_data
         {C : category}
         {PB : Pullbacks C}
         {d₁ d₂ : internal_cat PB}
         {f₁ f₂ : internal_functor d₁ d₂}
         (θ : internal_nat_trans f₁ f₂)
  : internal_nat_trans_data f₁ f₂
  := pr1 θ.

Definition internal_nat_trans_to_disp_nat_trans
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           {f₁ f₂ : internal_functor d₁ d₂}
           (θ : internal_nat_trans f₁ f₂)
  : disp_nat_trans
      (nat_trans_id _)
      (internal_functor_to_disp_functor f₁)
      (internal_functor_to_disp_functor f₂)
  := internal_nat_trans_data_to_disp_nat_trans θ ,, pr2 θ.

Proposition internal_nat_trans_commutes
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            {f₁ f₂ : internal_functor d₁ d₂}
            (θ : internal_nat_trans f₁ f₂)
            {Γ : C}
            {x₁ x₂ : Γ --> internal_cat_ob d₁}
            (g : internal_morphism x₁ x₂)
  : internal_functor_on_mor f₁ g ·i internal_nat_trans_morphism_ob θ x₂
    =
    internal_nat_trans_morphism_ob θ x₁ ·i internal_functor_on_mor f₂ g.
Proof.
  use internal_morphism_eq.
  pose proof (maponpaths pr1 (disp_nat_trans_ax (internal_nat_trans_to_disp_nat_trans θ) g)
              @ transportf_internal_morphism_mor_eq _ _ _ _)
    as path.
  cbn in path.
  refine (_ @ path @ _) ; cbn.
  - apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      rewrite !id_left.
      apply idpath.
  - apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      rewrite !id_left.
      apply idpath.
Qed.

Proposition internal_nat_trans_commutes_on_eq
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            {f₁ f₂ : internal_functor d₁ d₂}
            (θ : internal_nat_trans_data f₁ f₂)
            {Γ : C}
            {x y : Γ --> internal_cat_ob d₁}
            (p : x = y)
  : internal_nat_trans_morphism_ob θ x
    =
    eq_to_internal_morphism (maponpaths (λ z, z · _) p)
    ·i internal_nat_trans_morphism_ob θ y
    ·i eq_to_internal_morphism (maponpaths (λ z, z · _) (!p)).
Proof.
  induction p ; cbn.
  rewrite !eq_to_internal_morphism_id.
  rewrite internal_morphism_id_left, internal_morphism_id_right.
  apply idpath.
Qed.

Proposition make_internal_nat_trans_laws
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            {f₁ f₂ : internal_functor d₁ d₂}
            (θ : internal_nat_trans_data f₁ f₂)
            (p : ∏ (Γ : C)
                   (x₁ x₂ : Γ --> internal_cat_ob d₁)
                   (g : internal_morphism x₁ x₂),
                 internal_functor_on_mor f₁ g
                 ·i internal_nat_trans_morphism_ob θ x₂
                 =
                 internal_nat_trans_morphism_ob θ x₁
                 ·i internal_functor_on_mor f₂ g)
  : disp_nat_trans_axioms (internal_nat_trans_data_to_disp_nat_trans θ).
Proof.
  intros Γ₁ Γ₂ x₁ x₂ s g.
  refine (!_).
  use internal_morphism_over_eq.
  refine (transportf_internal_morphism_mor_eq _ _ _ _ @ _).
  refine (_ @ !(maponpaths pr1 (p _ _ _ (internal_morphism_over_to_internal_morphism g))) @ _) ;
    cbn.
  - apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      rewrite !id_left.
      apply idpath.
  - apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      rewrite assoc'.
      apply idpath.
Qed.

Proposition internal_nat_trans_eq
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            {f₁ f₂ : internal_functor d₁ d₂}
            {θ θ' : internal_nat_trans f₁ f₂}
            (p : internal_nat_trans_mor θ = internal_nat_trans_mor θ')
  : θ = θ'.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_disp_nat_trans_axioms.
  }
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; apply homset_property.
  }
  exact p.
Qed.

Proposition internal_nat_trans_eq'
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            {f₁ f₂ : internal_functor d₁ d₂}
            {θ θ' : internal_nat_trans f₁ f₂}
            (p : ∏ (Γ : C)
                   (x : Γ --> internal_cat_ob d₁),
                 internal_nat_trans_morphism_ob θ x
                 =
                 internal_nat_trans_morphism_ob θ' x)
  : θ = θ'.
Proof.
  use internal_nat_trans_eq.
  pose (maponpaths pr1 (p _ (identity _))) as q.
  cbn in q.
  rewrite !id_left in q.
  exact q.
Qed.

Proposition isaset_internal_nat_trans
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            (f₁ f₂ : internal_functor d₁ d₂)
  : isaset (internal_nat_trans f₁ f₂).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + apply homset_property.
    + intro.
      apply isasetaprop.
      apply isapropdirprod ; apply homset_property.
  - intro.
    apply isasetaprop.
    apply isaprop_disp_nat_trans_axioms.
Qed.

(** * 2. Examples of internal natural transformations *)
Section InternalNatTrans.
  Context {C : category}
          {PB : Pullbacks C}.

  Definition id_internal_nat_trans_data
             {d₁ d₂ : internal_cat PB}
             (f : internal_functor d₁ d₂)
    : internal_nat_trans_data f f.
  Proof.
    use make_internal_nat_trans_data.
    - exact (internal_functor_ob f · internal_cat_id _).
    - abstract
        (rewrite !assoc' ;
         rewrite internal_cat_id_dom ;
         apply id_right).
    - abstract
        (rewrite !assoc' ;
         rewrite internal_cat_id_cod ;
         apply id_right).
  Defined.

  Proposition id_internal_nat_trans_data_ob
              {d₁ d₂ : internal_cat PB}
              (f : internal_functor d₁ d₂)
              {Γ : C}
              (x : Γ --> internal_cat_ob d₁)
    : internal_nat_trans_morphism_ob (id_internal_nat_trans_data f) x = idi _.
  Proof.
    use internal_morphism_eq ; cbn.
    rewrite assoc'.
    apply idpath.
  Qed.

  Proposition id_internal_nat_trans_laws
              {d₁ d₂ : internal_cat PB}
              (f : internal_functor d₁ d₂)
    : disp_nat_trans_axioms
        (internal_nat_trans_data_to_disp_nat_trans
           (id_internal_nat_trans_data f)).
  Proof.
    use make_internal_nat_trans_laws.
    intros Γ x₁ x₂ g.
    rewrite !id_internal_nat_trans_data_ob.
    rewrite internal_morphism_id_left, internal_morphism_id_right.
    apply idpath.
  Qed.
  
  Definition id_internal_nat_trans
             {d₁ d₂ : internal_cat PB}
             (f : internal_functor d₁ d₂)
    : internal_nat_trans f f.
  Proof.
    use make_internal_nat_trans.
    - exact (id_internal_nat_trans_data f).
    - exact (id_internal_nat_trans_laws f).
  Defined.

  Proposition id_internal_nat_trans_ob
              {d₁ d₂ : internal_cat PB}
              (f : internal_functor d₁ d₂)
              {Γ : C}
              (x : Γ --> internal_cat_ob d₁)
    : internal_nat_trans_morphism_ob (id_internal_nat_trans f) x = idi _.
  Proof.
    exact (id_internal_nat_trans_data_ob f x).
  Qed.

  Definition internal_nat_trans_comp_data
             {d₁ d₂ : internal_cat PB}
             {f₁ f₂ f₃ : internal_functor d₁ d₂}
             (θ₁ : internal_nat_trans f₁ f₂)
             (θ₂ : internal_nat_trans f₂ f₃)
    : internal_nat_trans_data f₁ f₃.
  Proof.
    use make_internal_nat_trans_data.
    - refine (PullbackArrow _ _ θ₁ θ₂ _ · internal_cat_comp d₂).
      abstract
        (rewrite internal_nat_trans_dom, internal_nat_trans_cod ;
         apply idpath).
    - abstract
        (rewrite !assoc' ;
         rewrite internal_cat_comp_dom ;
         rewrite !assoc ;
         rewrite PullbackArrow_PullbackPr1 ;
         rewrite internal_nat_trans_dom ;
         apply idpath).
    - abstract
        (rewrite !assoc' ;
         rewrite internal_cat_comp_cod ;
         rewrite !assoc ;
         rewrite PullbackArrow_PullbackPr2 ;
         rewrite internal_nat_trans_cod ;
         apply idpath).
  Defined.

  Proposition comp_internal_nat_trans_data_ob
              {d₁ d₂ : internal_cat PB}
              {f₁ f₂ f₃ : internal_functor d₁ d₂}
              (θ₁ : internal_nat_trans f₁ f₂)
              (θ₂ : internal_nat_trans f₂ f₃)
              {Γ : C}
              (x : Γ --> internal_cat_ob d₁)
    : internal_nat_trans_morphism_ob (internal_nat_trans_comp_data θ₁ θ₂) x
      =
      internal_nat_trans_morphism_ob θ₁ x ·i internal_nat_trans_morphism_ob θ₂ x.
  Proof.
    use internal_morphism_eq ; cbn.
    rewrite !assoc.
    apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    - rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr2.
      apply idpath.
  Qed.

  Proposition internal_nat_trans_comp_laws
              {d₁ d₂ : internal_cat PB}
              {f₁ f₂ f₃ : internal_functor d₁ d₂}
              (θ₁ : internal_nat_trans f₁ f₂)
              (θ₂ : internal_nat_trans f₂ f₃)
    : disp_nat_trans_axioms
        (internal_nat_trans_data_to_disp_nat_trans
           (internal_nat_trans_comp_data θ₁ θ₂)).
  Proof.
    use make_internal_nat_trans_laws.
    intros Γ x₁ x₂ g.
    rewrite !comp_internal_nat_trans_data_ob.
    rewrite internal_morphism_assoc.
    rewrite internal_nat_trans_commutes.
    rewrite !internal_morphism_assoc'.
    rewrite internal_nat_trans_commutes.
    apply idpath.
  Qed.
  
  Definition internal_nat_trans_comp
             {d₁ d₂ : internal_cat PB}
             {f₁ f₂ f₃ : internal_functor d₁ d₂}
             (θ₁ : internal_nat_trans f₁ f₂)
             (θ₂ : internal_nat_trans f₂ f₃)
    : internal_nat_trans f₁ f₃.
  Proof.
    use make_internal_nat_trans.
    - exact (internal_nat_trans_comp_data θ₁ θ₂).
    - exact (internal_nat_trans_comp_laws θ₁ θ₂).
  Defined.

  Proposition comp_internal_nat_trans_ob
              {d₁ d₂ : internal_cat PB}
              {f₁ f₂ f₃ : internal_functor d₁ d₂}
              (θ₁ : internal_nat_trans f₁ f₂)
              (θ₂ : internal_nat_trans f₂ f₃)
              {Γ : C}
              (x : Γ --> internal_cat_ob d₁)
    : internal_nat_trans_morphism_ob (internal_nat_trans_comp θ₁ θ₂) x
      =
      internal_nat_trans_morphism_ob θ₁ x ·i internal_nat_trans_morphism_ob θ₂ x.
  Proof.
    apply comp_internal_nat_trans_data_ob.
  Qed.

  Definition internal_nat_trans_lwhisker_data
             {d₁ d₂ d₃ : internal_cat PB}
             (f : internal_functor d₁ d₂)
             {g₁ g₂ : internal_functor d₂ d₃}
             (θ : internal_nat_trans g₁ g₂)
    : internal_nat_trans_data
        (comp_internal_functor f g₁)
        (comp_internal_functor f g₂).
  Proof.
    use make_internal_nat_trans_data.
    - exact (internal_functor_ob f · θ).
    - abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite internal_nat_trans_dom ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite internal_nat_trans_cod ;
         apply idpath).
  Defined.

  Proposition internal_nat_trans_lwhisker_data_ob
              {d₁ d₂ d₃ : internal_cat PB}
              (f : internal_functor d₁ d₂)
              {g₁ g₂ : internal_functor d₂ d₃}
              (θ : internal_nat_trans g₁ g₂)
              {Γ : C}
              (x : Γ --> internal_cat_ob d₁)
    : internal_nat_trans_morphism_ob (internal_nat_trans_lwhisker_data f θ) x
      =
      eq_to_internal_morphism (assoc _ _ _)
      ·i internal_nat_trans_morphism_ob θ (x · internal_functor_ob f)
      ·i eq_to_internal_morphism (assoc' _ _ _).
  Proof.
    refine (!(internal_morphism_id_right _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (eq_to_internal_morphism_inv (assoc' _ _ _) (assoc _ _ _)).
    }
    rewrite internal_morphism_assoc.
    apply maponpaths_2.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_left, eq_to_internal_morphism_right.
    cbn.
    apply assoc.
  Qed.

  Proposition internal_nat_trans_lwhisker_laws
              {d₁ d₂ d₃ : internal_cat PB}
              (f : internal_functor d₁ d₂)
              {g₁ g₂ : internal_functor d₂ d₃}
              (θ : internal_nat_trans g₁ g₂)
    : disp_nat_trans_axioms
        (internal_nat_trans_data_to_disp_nat_trans
           (internal_nat_trans_lwhisker_data f θ)).
  Proof.
    use make_internal_nat_trans_laws.
    intros Γ x₁ x₂ g.
    rewrite !internal_nat_trans_lwhisker_data_ob.
    rewrite !internal_morphism_assoc.
    rewrite comp_internal_functor_on_mor.
    rewrite !internal_morphism_assoc'.
    apply maponpaths.
    rewrite !internal_morphism_assoc.
    etrans.
    {
      apply maponpaths_2.
      exact (internal_nat_trans_commutes θ (internal_functor_on_mor f g)).
    }
    rewrite !internal_morphism_assoc'.
    apply maponpaths.
    refine (!_).
    apply comp_internal_functor_on_mor'.
  Qed.
  
  Definition internal_nat_trans_lwhisker
             {d₁ d₂ d₃ : internal_cat PB}
             (f : internal_functor d₁ d₂)
             {g₁ g₂ : internal_functor d₂ d₃}
             (θ : internal_nat_trans g₁ g₂)
    : internal_nat_trans
        (comp_internal_functor f g₁)
        (comp_internal_functor f g₂).
  Proof.
    use make_internal_nat_trans.
    - exact (internal_nat_trans_lwhisker_data f θ).
    - exact (internal_nat_trans_lwhisker_laws f θ).
  Defined.

  Proposition internal_nat_trans_lwhisker_ob
              {d₁ d₂ d₃ : internal_cat PB}
              (f : internal_functor d₁ d₂)
              {g₁ g₂ : internal_functor d₂ d₃}
              (θ : internal_nat_trans g₁ g₂)
              {Γ : C}
              (x : Γ --> internal_cat_ob d₁)
    : internal_nat_trans_morphism_ob (internal_nat_trans_lwhisker f θ) x
      =
      eq_to_internal_morphism (assoc _ _ _)
      ·i internal_nat_trans_morphism_ob θ (x · internal_functor_ob f)
      ·i eq_to_internal_morphism (assoc' _ _ _).
  Proof.
    apply internal_nat_trans_lwhisker_data_ob.
  Qed.

  Definition internal_nat_trans_rwhisker_data
             {d₁ d₂ d₃ : internal_cat PB}
             {f₁ f₂ : internal_functor d₁ d₂}
             (θ : internal_nat_trans f₁ f₂)
             (g : internal_functor d₂ d₃)
    : internal_nat_trans_data
        (comp_internal_functor f₁ g)
        (comp_internal_functor f₂ g).
  Proof.
    use make_internal_nat_trans_data.
    - exact (θ · internal_functor_mor g).
    - abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite internal_functor_mor_dom ;
         rewrite !assoc ;
         rewrite internal_nat_trans_dom ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite !assoc' ;
         rewrite internal_functor_mor_cod ;
         rewrite !assoc ;
         rewrite internal_nat_trans_cod ;
         apply idpath).
  Defined.

  Proposition internal_nat_trans_rwhisker_data_ob
              {d₁ d₂ d₃ : internal_cat PB}
              {f₁ f₂ : internal_functor d₁ d₂}
              (θ : internal_nat_trans f₁ f₂)
              (g : internal_functor d₂ d₃)
              {Γ : C}
              (x : Γ --> internal_cat_ob d₁)
    : internal_nat_trans_morphism_ob (internal_nat_trans_rwhisker_data θ g) x
      =
      eq_to_internal_morphism (assoc _ _ _)
      ·i internal_functor_on_mor g (internal_nat_trans_morphism_ob θ x)
      ·i eq_to_internal_morphism (assoc' _ _ _).
  Proof.
    refine (!(internal_morphism_id_right _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (eq_to_internal_morphism_inv (assoc' _ _ _) (assoc _ _ _)).
    }
    rewrite internal_morphism_assoc.
    apply maponpaths_2.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_left, eq_to_internal_morphism_right.
    cbn.
    apply assoc.
  Qed.

  Proposition internal_nat_trans_rwhisker_laws
              {d₁ d₂ d₃ : internal_cat PB}
              {f₁ f₂ : internal_functor d₁ d₂}
              (θ : internal_nat_trans f₁ f₂)
              (g : internal_functor d₂ d₃)
    : disp_nat_trans_axioms
        (internal_nat_trans_data_to_disp_nat_trans
           (internal_nat_trans_rwhisker_data θ g)).
  Proof.
    use make_internal_nat_trans_laws.
    intros Γ x₁ x₂ h.
    rewrite !internal_nat_trans_rwhisker_data_ob.
    rewrite !internal_morphism_assoc.
    rewrite comp_internal_functor_on_mor.
    rewrite !internal_morphism_assoc'.
    apply maponpaths.
    rewrite !internal_morphism_assoc.
    rewrite <- internal_functor_comp.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      exact (internal_nat_trans_commutes θ h).
    }
    rewrite internal_functor_comp.
    rewrite !internal_morphism_assoc'.
    apply maponpaths.
    refine (!_).
    apply comp_internal_functor_on_mor'.
  Qed.

  Definition internal_nat_trans_rwhisker
             {d₁ d₂ d₃ : internal_cat PB}
             {f₁ f₂ : internal_functor d₁ d₂}
             (θ : internal_nat_trans f₁ f₂)
             (g : internal_functor d₂ d₃)
    : internal_nat_trans
        (comp_internal_functor f₁ g)
        (comp_internal_functor f₂ g).
  Proof.
    use make_internal_nat_trans.
    - exact (internal_nat_trans_rwhisker_data θ g).
    - exact (internal_nat_trans_rwhisker_laws θ g).
  Defined.

  Proposition internal_nat_trans_rwhisker_ob
              {d₁ d₂ d₃ : internal_cat PB}
              {f₁ f₂ : internal_functor d₁ d₂}
              (θ : internal_nat_trans f₁ f₂)
              (g : internal_functor d₂ d₃)
              {Γ : C}
              (x : Γ --> internal_cat_ob d₁)
    : internal_nat_trans_morphism_ob (internal_nat_trans_rwhisker θ g) x
      =
      eq_to_internal_morphism (assoc _ _ _)
      ·i internal_functor_on_mor g (internal_nat_trans_morphism_ob θ x)
      ·i eq_to_internal_morphism (assoc' _ _ _).
  Proof.
    refine (!(internal_morphism_id_right _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (eq_to_internal_morphism_inv (assoc' _ _ _) (assoc _ _ _)).
    }
    rewrite internal_morphism_assoc.
    apply maponpaths_2.
    use internal_morphism_eq.
    rewrite eq_to_internal_morphism_left, eq_to_internal_morphism_right.
    cbn.
    apply assoc.
  Qed.
End InternalNatTrans.
