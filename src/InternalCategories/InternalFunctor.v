Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Require Import InternalCategories.InternalCat.

Local Open Scope cat.

(** * 1. Diagrams of internal functors *)
Definition internal_functor_diag
           {C : category}
           (d₁ d₂ : internal_cat_diag C)
  : UU
  := internal_cat_ob d₁ --> internal_cat_ob d₂
     ×
     internal_cat_mor d₁ --> internal_cat_mor d₂.

Definition internal_functor_ob
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (f : internal_functor_diag d₁ d₂)
  : internal_cat_ob d₁ --> internal_cat_ob d₂
  := pr1 f.

Definition internal_functor_mor
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (f : internal_functor_diag d₁ d₂)
  : internal_cat_mor d₁ --> internal_cat_mor d₂
  := pr2 f.

Definition internal_functor_data
           {C : category}
           (d₁ d₂ : internal_cat_diag C)
  : UU
  := ∑ (f : internal_functor_diag d₁ d₂),
     (internal_functor_mor f · internal_cat_dom d₂
      =
      internal_cat_dom d₁ · internal_functor_ob f)
     ×
     (internal_functor_mor f · internal_cat_cod d₂
      =
      internal_cat_cod d₁ · internal_functor_ob f).

Definition make_internal_functor_data
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (f : internal_functor_diag d₁ d₂)
           (p : internal_functor_mor f · internal_cat_dom d₂
                =
                internal_cat_dom d₁ · internal_functor_ob f)
           (q : internal_functor_mor f · internal_cat_cod d₂
                =
                internal_cat_cod d₁ · internal_functor_ob f)
  : internal_functor_data d₁ d₂
  := f ,, (p ,, q).
           
Coercion internal_functor_data_to_diag
         {C : category}
         {d₁ d₂ : internal_cat_diag C}
         (f : internal_functor_data d₁ d₂)
  : internal_functor_diag d₁ d₂
  := pr1 f.

Definition internal_functor_mor_dom
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (f : internal_functor_data d₁ d₂)
  : internal_functor_mor f · internal_cat_dom d₂
    =
    internal_cat_dom d₁ · internal_functor_ob f
  := pr12 f.

Definition internal_functor_mor_cod
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (f : internal_functor_data d₁ d₂)
  : internal_functor_mor f · internal_cat_cod d₂
    =
    internal_cat_cod d₁ · internal_functor_ob f
  := pr22 f.

Definition internal_functor_on_mor_over
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (f : internal_functor_data d₁ d₂)
           {Γ Δ : C}
           {x : Γ --> internal_cat_ob d₁}
           {y : Δ --> internal_cat_ob d₁}
           {s : Γ --> Δ}
           (g : internal_morphism_over x y s)
  : internal_morphism_over (x · internal_functor_ob f) (y · internal_functor_ob f) s.
Proof.
  use make_internal_morphism_over.
  - exact (g · internal_functor_mor f).
  - abstract
      (rewrite !assoc' ;
       rewrite internal_functor_mor_dom ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       exact (internal_morphism_over_dom g)).
  - abstract
      (rewrite !assoc' ;
       rewrite internal_functor_mor_cod ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       exact (internal_morphism_over_cod g)).
Defined.

Definition internal_functor_on_mor
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (f : internal_functor_data d₁ d₂)
           {Γ : C}
           {x y : Γ --> internal_cat_ob d₁}
           (g : internal_morphism x y)
  : internal_morphism (x · internal_functor_ob f) (y · internal_functor_ob f).
Proof.
  use make_internal_morphism.
  - exact (g · internal_functor_mor f).
  - abstract
      (rewrite !assoc' ;
       rewrite internal_functor_mor_dom ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       exact (internal_morphism_dom g)).
  - abstract
      (rewrite !assoc' ;
       rewrite internal_functor_mor_cod ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       exact (internal_morphism_cod g)).
Defined.

Definition internal_functor_to_disp_functor_data
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           (f : internal_functor_data d₁ d₂)
  : disp_functor_data
      (functor_identity _)
      (internal_cat_disp_cat d₁)
      (internal_cat_disp_cat d₂).
Proof.
  simple refine (_ ,, _).
  - exact (λ Γ x, x · internal_functor_ob f).
  - exact (λ Γ Δ x y s g, internal_functor_on_mor_over f g).
Defined.

(** * 2. Internal functors *)
Definition internal_functor
           {C : category}
           {PB : Pullbacks C}
           (d₁ d₂ : internal_cat PB)
  : UU
  := ∑ (f : internal_functor_data d₁ d₂),
     disp_functor_axioms (internal_functor_to_disp_functor_data f).

Proposition isaset_internal_functor
            {C : category}
            {PB : Pullbacks C}
            (d₁ d₂ : internal_cat PB)
  : isaset (internal_functor d₁ d₂).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + use isaset_dirprod.
      * apply homset_property.
      * apply homset_property.
    + intro.
      apply isasetaprop.
      apply isapropdirprod.
      * apply homset_property.
      * apply homset_property.
  - intro.
    apply isasetaprop.
    apply isaprop_disp_functor_axioms.
Qed.

Definition make_internal_functor
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           (f : internal_functor_data d₁ d₂)
           (p : disp_functor_axioms (internal_functor_to_disp_functor_data f))
  : internal_functor d₁ d₂
  := f ,, p.

Coercion internal_functor_to_data
         {C : category}
         {PB : Pullbacks C}
         {d₁ d₂ : internal_cat PB}
         (f : internal_functor d₁ d₂)
  : internal_functor_data d₁ d₂
  := pr1 f.

Definition internal_functor_to_disp_functor
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           (f : internal_functor d₁ d₂)
  : disp_functor
      (functor_identity _)
      (internal_cat_disp_cat d₁)
      (internal_cat_disp_cat d₂).
Proof.
  simple refine (_ ,, _).
  - exact (internal_functor_to_disp_functor_data f).
  - exact (pr2 f).
Defined.

Proposition internal_functor_eq
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            {f₁ f₂ : internal_functor d₁ d₂}
            (p : internal_functor_ob f₁ = internal_functor_ob f₂)
            (q : internal_functor_mor f₁ = internal_functor_mor f₂)
  : f₁ = f₂.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_disp_functor_axioms.
  }
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; apply homset_property.
  }
  use pathsdirprod.
  - exact p.
  - exact q.
Qed.

Proposition internal_functor_id
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            (f : internal_functor d₁ d₂)
            {Γ : C}
            (x : Γ --> internal_cat_ob d₁)
  : internal_functor_on_mor f (idi x) = idi _.
Proof.
  use internal_morphism_eq.
  pose proof (disp_functor_id (internal_functor_to_disp_functor f) x)
    as p.
  exact (maponpaths pr1 p).
Qed.

Proposition internal_functor_comp
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            (f : internal_functor d₁ d₂)
            {Γ : C}
            {x₁ x₂ x₃ : Γ --> internal_cat_ob d₁}
            (g₁ : internal_morphism x₁ x₂)
            (g₂ : internal_morphism x₂ x₃)
  : internal_functor_on_mor f (g₁ ·i g₂)
    =
    internal_functor_on_mor f g₁ ·i internal_functor_on_mor f g₂.
Proof.
  use internal_morphism_eq.
  pose proof (maponpaths pr1 (disp_functor_comp (internal_functor_to_disp_functor f) g₁ g₂))
    as r.
  cbn in r.
  refine (_ @ r @ _) ; cbn.
  - do 2 apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      rewrite id_left.
      apply idpath.
  - apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      rewrite id_left.
      apply idpath.
Qed.

Proposition internal_functor_eq_to_internal_morphism
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            (f : internal_functor d₁ d₂)
            {Γ : C}
            {x₁ x₂ : Γ --> internal_cat_ob d₁}
            (p : x₁ = x₂)
  : internal_functor_on_mor f (eq_to_internal_morphism p)
    =
    eq_to_internal_morphism (maponpaths (λ z, z · _) p).
Proof.
  induction p ; cbn.
  rewrite !eq_to_internal_morphism_id.
  rewrite internal_functor_id.
  apply idpath.
Qed.

Proposition internal_functor_eq_to_internal_morphism_over
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            (f : internal_functor d₁ d₂)
            {Γ : C}
            {x₁ x₂ : Γ --> internal_cat_ob d₁}
            (p : x₁ = x₂)
  : internal_functor_on_mor_over f (eq_to_internal_morphism p)
    =
    eq_to_internal_morphism (maponpaths (λ z, z · _) p).
Proof.
  induction p ; cbn.
  rewrite !eq_to_internal_morphism_id.
  rewrite <- internal_functor_id.
  use internal_morphism_eq ; cbn.
  apply idpath.
Qed.

Definition make_internal_functor_axioms
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ : internal_cat PB}
           (f : internal_functor_data d₁ d₂)
           (fid : ∏ (Γ : C)
                    (x : Γ --> internal_cat_ob d₁),
                  internal_functor_on_mor f (idi x) = idi _)
           (fcomp : ∏ (Γ : C)
                      (x₁ x₂ x₃ : Γ --> internal_cat_ob d₁)
                      (g₁ : internal_morphism x₁ x₂)
                      (g₂ : internal_morphism x₂ x₃),
                    internal_functor_on_mor f (g₁ ·i g₂)
                    =
                    internal_functor_on_mor f g₁ ·i internal_functor_on_mor f g₂)
  : disp_functor_axioms (internal_functor_to_disp_functor_data f).
Proof.
  split.
  - intros Γ x.
    use internal_morphism_eq.
    exact (maponpaths pr1 (fid Γ x)).
  - intros Γ₁ Γ₂ Γ₃ x₁ x₂ x₃ s₁ s₂ g₁ g₂.
    use internal_morphism_over_eq.
    cbn.
    pose (g₁' := internal_morphism_over_to_internal_morphism g₁).
    pose (g₂' := internal_morphism_over_to_internal_morphism
                   (internal_morphism_over_precomp g₂ s₁)).
    refine (_ @ maponpaths pr1 (fcomp _ _ _ _ g₁' g₂') @ _) ; cbn.
    + do 2 apply maponpaths_2.
      apply maponpaths.
      apply homset_property.
    + apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      * rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      * rewrite PullbackArrow_PullbackPr2.
        rewrite assoc'.
        apply idpath.
Qed.

(** * 3. The identity and composition of internal functors *)
Definition identity_internal_functor
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat PB)
  : internal_functor d d.
Proof.
  use make_internal_functor.
  - use make_internal_functor_data.
    + split.
      * exact (identity _).
      * exact (identity _).
    + abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    + abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  - use make_internal_functor_axioms.
    + abstract
        (intros Γ x ;
         use internal_morphism_eq ; cbn ;
         rewrite !id_right ;
         apply idpath).
    + abstract
        (intros Γ x₁ x₂ x₃ g₁ g₂ ;
         use internal_morphism_eq ; cbn ;
         rewrite id_right ;
         apply maponpaths_2 ;
         use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))) ;
         [ rewrite PullbackArrow_PullbackPr1 | rewrite PullbackArrow_PullbackPr2 ] ;
         rewrite id_right ;
         apply idpath).
Defined.

Proposition identity_internal_functor_on_mor
            {C : category}
            {PB : Pullbacks C}
            (d : internal_cat PB)
            {Γ : C}
            {x₁ x₂ : Γ --> internal_cat_ob d}
            (f : internal_morphism x₁ x₂)
  : internal_morphism_to_mor (internal_functor_on_mor (identity_internal_functor d) f)
    =
    f.
Proof.
  cbn.
  apply id_right.
Qed.

Definition comp_internal_functor_data
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ d₃ : internal_cat PB}
           (f₁ : internal_functor d₁ d₂)
           (f₂ : internal_functor d₂ d₃)
  : internal_functor_data d₁ d₃.
Proof.
  use make_internal_functor_data.
  - split.
    + exact (internal_functor_ob f₁ · internal_functor_ob f₂).
    + exact (internal_functor_mor f₁ · internal_functor_mor f₂).
  - abstract
      (cbn ;
       rewrite !assoc' ;
       rewrite internal_functor_mor_dom ;
       rewrite !assoc ;
       rewrite internal_functor_mor_dom ;
       apply idpath).
  - abstract
      (cbn ;
       rewrite !assoc' ;
       rewrite internal_functor_mor_cod ;
       rewrite !assoc ;
       rewrite internal_functor_mor_cod ;
       apply idpath).
Defined.

Proposition comp_internal_functor_data_on_mor
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ d₃ : internal_cat PB}
            (f₁ : internal_functor d₁ d₂)
            (f₂ : internal_functor d₂ d₃)
            {Γ : C}
            {x₁ x₂ : Γ --> internal_cat_ob d₁}
            (g : internal_morphism x₁ x₂)
  : internal_morphism_to_mor (internal_functor_on_mor (comp_internal_functor_data f₁ f₂) g)
    =
    internal_functor_on_mor f₂ (internal_functor_on_mor f₁ g).
Proof.
  cbn.
  rewrite assoc'.
  apply idpath.
Qed.
  
Proposition comp_internal_functor_laws
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ d₃ : internal_cat PB}
            (f₁ : internal_functor d₁ d₂)
            (f₂ : internal_functor d₂ d₃)
  : disp_functor_axioms
      (internal_functor_to_disp_functor_data
         (comp_internal_functor_data f₁ f₂)).
Proof.
  use make_internal_functor_axioms.
  - intros Γ x.
    use internal_morphism_eq.
    rewrite comp_internal_functor_data_on_mor.
    rewrite !internal_functor_id.
    cbn.
    rewrite !assoc'.
    apply idpath.
  - intros Γ x₁ x₂ x₃ g₁ g₂ ; cbn in x₁, x₂, x₃, g₁, g₂.
    use internal_morphism_eq.
    rewrite comp_internal_functor_data_on_mor.
    rewrite !internal_functor_comp.
    cbn.
    apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      cbn.
      rewrite !assoc'.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      cbn.
      rewrite !assoc'.
      apply idpath.
Qed.

Definition comp_internal_functor
           {C : category}
           {PB : Pullbacks C}
           {d₁ d₂ d₃ : internal_cat PB}
           (f₁ : internal_functor d₁ d₂)
           (f₂ : internal_functor d₂ d₃)
  : internal_functor d₁ d₃.
Proof.
  use make_internal_functor.
  - exact (comp_internal_functor_data f₁ f₂).
  - apply comp_internal_functor_laws.
Defined.

Proposition comp_internal_functor_on_mor
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ d₃ : internal_cat PB}
            (f₁ : internal_functor d₁ d₂)
            (f₂ : internal_functor d₂ d₃)
            {Γ : C}
            {x₁ x₂ : Γ --> internal_cat_ob d₁}
            (g : internal_morphism x₁ x₂)
  : internal_functor_on_mor (comp_internal_functor f₁ f₂) g
    ·i eq_to_internal_morphism (assoc _ _ _)
    =
    eq_to_internal_morphism (assoc _ _ _)
    ·i internal_functor_on_mor f₂ (internal_functor_on_mor f₁ g).
Proof.
  use internal_morphism_eq.
  rewrite eq_to_internal_morphism_left, eq_to_internal_morphism_right.
  exact (comp_internal_functor_data_on_mor f₁ f₂ g).
Qed.

Proposition comp_internal_functor_on_mor'
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ d₃ : internal_cat PB}
            (f₁ : internal_functor d₁ d₂)
            (f₂ : internal_functor d₂ d₃)
            {Γ : C}
            {x₁ x₂ : Γ --> internal_cat_ob d₁}
            (g : internal_morphism x₁ x₂)
  : eq_to_internal_morphism (assoc' _ _ _)
    ·i internal_functor_on_mor (comp_internal_functor f₁ f₂) g
    =
    internal_functor_on_mor f₂ (internal_functor_on_mor f₁ g)
    ·i eq_to_internal_morphism (assoc' _ _ _).
Proof.
  refine (!(internal_morphism_id_right _) @ _).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    exact (eq_to_internal_morphism_inv (assoc' _ _ _) (assoc _ _ _)).
  }
  rewrite !internal_morphism_assoc.
  apply maponpaths_2.
  rewrite !internal_morphism_assoc'.
  etrans.
  {
    apply maponpaths.
    apply comp_internal_functor_on_mor.
  }
  rewrite internal_morphism_assoc.
  rewrite eq_to_internal_morphism_inv.
  rewrite internal_morphism_id_left.
  apply idpath.
Qed.

Proposition comp_internal_functor_on_mor_to_mor
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ d₃ : internal_cat PB}
            (f₁ : internal_functor d₁ d₂)
            (f₂ : internal_functor d₂ d₃)
            {Γ : C}
            {x₁ x₂ : Γ --> internal_cat_ob d₁}
            (g : internal_morphism x₁ x₂)
  : internal_morphism_to_mor (internal_functor_on_mor (comp_internal_functor f₁ f₂) g)
    =
    internal_functor_on_mor f₂ (internal_functor_on_mor f₁ g).
Proof.
  apply comp_internal_functor_data_on_mor.
Qed.

(** * 4. Internal functors induce Cartesian functors *)
Proposition internal_functor_id'
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            (f : internal_functor d₁ d₂)
  : internal_cat_id d₁ · internal_functor_mor f
    =
    internal_functor_ob f · internal_cat_id d₂.
Proof.
  pose proof (disp_functor_id (internal_functor_to_disp_functor f) (identity _))
    as p.
  refine (_ @ maponpaths pr1 p @ _).
  - cbn.
    rewrite id_left.
    apply idpath.
  - cbn.
    rewrite id_left.
    apply idpath.
Qed.

Section InternalFunctorCartesian.
  Context {C : category}
          {PB : Pullbacks C}
          {d₁ d₂ : internal_cat PB}
          (f : internal_functor d₁ d₂).

  Definition internal_functor_img_factorisation
             {Γ₁ Γ₂ Γ₃ : C}
             {s₁ : Γ₁ --> Γ₂}
             {s₂ : Γ₂ --> Γ₃}
             {x : Γ₃ --> internal_cat_ob d₁}
             {y : Γ₁ --> internal_cat_ob d₂}
             (g : internal_morphism_over y (x · internal_functor_ob f) (s₁ · s₂))
    : internal_morphism_over y (internal_cat_lift d₁ s₂ x · internal_functor_ob f) s₁.
  Proof.
    use make_internal_morphism_over.
    - exact g.
    - abstract
        (apply internal_morphism_over_dom).
    - abstract
        (rewrite internal_morphism_over_cod ;
         unfold internal_cat_lift ;
         rewrite !assoc' ;
         apply idpath).
  Defined.      
    
  Definition is_cartesian_disp_functor_internal_functor               
    : is_cartesian_disp_functor (internal_functor_to_disp_functor f).
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact (internal_cat_to_cleaving d₁).
    }
    intros Γ₂ Γ₃ s₂ x Γ₁ s₁ y g.
    use iscontraprop1.
    * abstract
        (use invproofirrelevance ;
         intros ζ₁ ζ₂ ;
         use subtypePath ; [ intro ; apply homsets_disp | ] ;
         use internal_morphism_over_eq ;
         pose proof (maponpaths (λ z, pr1 z) (pr2 ζ₁ @ !(pr2 ζ₂))) as p ;
         cbn in p ;
         refine (!_ @ p @ _) ;
         (apply internal_morphism_id_right_pb ; [ apply idpath | ] ;
          cbn ;
          unfold internal_cat_lift ;
          rewrite !assoc' ;
          rewrite internal_functor_id' ;
          apply idpath)).
    * refine (internal_functor_img_factorisation g ,, _).
      abstract
        (use internal_morphism_over_eq ;
         cbn ;
         use internal_morphism_id_right_pb ; [ apply idpath | ] ;
         rewrite !assoc' ;
         rewrite internal_functor_id' ;
         apply idpath).
  Defined.

  Definition preserves_cleaving_internal_functor_to_disp_functor
    : preserves_cleaving
        (internal_cat_to_cleaving d₁)
        (internal_cat_to_cleaving d₂)
        (internal_functor_to_disp_functor f).
  Proof.
    use make_preserves_cleaving.
    - intros Γ₁ Γ₂ s x ; cbn ; unfold internal_cat_lift.
      apply assoc'.
    - intros Γ₁ Γ₂ s x ; cbn -[idtoiso_disp].
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply idtoiso_disp_eq_to_internal_morphism.
      }
      use internal_morphism_over_eq.
      rewrite eq_to_internal_morphism_left_over.
      refine (!_).
      refine (transportf_internal_morphism_mor_eq _ _ _ _ @ _).
      refine (maponpaths pr1 (internal_functor_id f (s · x)) @ _).
      cbn.
      rewrite !assoc'.
      apply idpath.
  Qed.
End InternalFunctorCartesian.
