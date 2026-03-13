Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import InternalCategories.InternalCat.
Require Import InternalCategories.InternalFunctor.

Local Open Scope cat.

(** * 1. The category of internal categories *)
Proposition internal_functor_id_left
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            (f : internal_functor d₁ d₂)
  : comp_internal_functor (identity_internal_functor _) f = f.
Proof.
  use internal_functor_eq ; cbn.
  - rewrite id_left.
    apply idpath.
  - rewrite id_left.
    apply idpath.
Qed.      

Proposition internal_functor_id_right
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat PB}
            (f : internal_functor d₁ d₂)
  : comp_internal_functor f (identity_internal_functor _) = f.
Proof.
  use internal_functor_eq ; cbn.
  - rewrite id_right.
    apply idpath.
  - rewrite id_right.
    apply idpath.
Qed.      

Proposition internal_functor_assoc
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ d₃ d₄ : internal_cat PB}
            (f₁ : internal_functor d₁ d₂)
            (f₂ : internal_functor d₂ d₃)
            (f₃ : internal_functor d₃ d₄)
  : comp_internal_functor f₁ (comp_internal_functor f₂ f₃)
    =
    comp_internal_functor (comp_internal_functor f₁ f₂) f₃.
Proof.
  use internal_functor_eq ; cbn.
  - rewrite assoc'.
    apply idpath.
  - rewrite assoc'.
    apply idpath.
Qed.

Definition precat_ob_mor_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (internal_cat PB).
  - exact internal_functor.
Defined.

Definition precat_data_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact (precat_ob_mor_of_internal_cat PB).
  - exact identity_internal_functor.
  - exact (λ _ _ _ f₁ f₂, comp_internal_functor f₁ f₂).
Defined.

Proposition precat_of_internal_cat_laws
            {C : category}
            (PB : Pullbacks C)
  : is_precategory_one_assoc (precat_data_of_internal_cat PB).
Proof.
  repeat split ; intros.
  - apply internal_functor_id_left.
  - apply internal_functor_id_right.
  - apply internal_functor_assoc.
Qed.
  
Definition precat_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : precategory.
Proof.
  use make_precategory_one_assoc.
  - exact (precat_data_of_internal_cat PB).
  - exact (precat_of_internal_cat_laws PB).
Defined.

Definition cat_of_internal_cat
           {C : category}
           (PB : Pullbacks C)
  : category.
Proof.
  use make_category.
  - exact (precat_of_internal_cat PB).
  - abstract
      (intros d₁ d₂ ; cbn ;
       apply isaset_internal_functor).
Defined.

(** * 2. Paths of internal categories *)
Definition path_of_internal_cat_diag
           {C : category}
           (d₁ d₂ : internal_cat_diag C)
  : UU
  := ∑ (p : internal_cat_ob d₁ = internal_cat_ob d₂)
       (q : internal_cat_mor d₁ = internal_cat_mor d₂),
     (internal_cat_dom d₁ · idtoiso p = idtoiso q · internal_cat_dom d₂)
     ×
     (internal_cat_cod d₁ · idtoiso p = idtoiso q · internal_cat_cod d₂).

Definition path_of_internal_cat_diag_ob
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (p : path_of_internal_cat_diag d₁ d₂)
  : internal_cat_ob d₁ = internal_cat_ob d₂
  := pr1 p.

Definition path_of_internal_cat_diag_mor
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (p : path_of_internal_cat_diag d₁ d₂)
  : internal_cat_mor d₁ = internal_cat_mor d₂
  := pr12 p.

Definition path_of_internal_cat_diag_dom
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (p : path_of_internal_cat_diag d₁ d₂)
  : internal_cat_dom d₁ · idtoiso (path_of_internal_cat_diag_ob p)
    =
    idtoiso (path_of_internal_cat_diag_mor p) · internal_cat_dom d₂
  := pr122 p.

Definition path_of_internal_cat_diag_cod
           {C : category}
           {d₁ d₂ : internal_cat_diag C}
           (p : path_of_internal_cat_diag d₁ d₂)
  : internal_cat_cod d₁ · idtoiso (path_of_internal_cat_diag_ob p)
    =
    idtoiso (path_of_internal_cat_diag_mor p) · internal_cat_cod d₂
  := pr222 p.

Definition internal_cat_diag_eq
           {C : category}
           (d₁ d₂ : internal_cat_diag C)
  : (d₁ = d₂) ≃ path_of_internal_cat_diag d₁ d₂.
Proof.
  induction d₁ as [ o₁ [ m₁ [ s₁ t₁ ]]].
  induction d₂ as [ o₂ [ m₂ [ s₂ t₂ ]]].
  cbn.
  refine (_ ∘ total2_paths_equiv _ _ _)%weq.
  use weqfibtototal.
  intro p ; cbn in p.
  induction p ; cbn.
  refine (_ ∘ total2_paths_equiv _ _ _)%weq.
  use weqfibtototal.
  intro p ; cbn in p.
  induction p ; cbn.
  refine (_ ∘ pathsdirprodweq)%weq.
  use weqdirprodf.
  - rewrite id_left, id_right.
    exact (idweq _).
  - rewrite id_left, id_right.
    exact (idweq _).
Defined.

Lemma internal_cat_eq_comp
      {C : category}
      {PB : Pullbacks C}
      {d₁ d₂ : internal_cat_data PB}
      {p : internal_cat_ob d₁ --> internal_cat_ob d₂}
      {q : internal_cat_mor d₁ --> internal_cat_mor d₂}
      (r₁ : internal_cat_dom d₁ · p = q · internal_cat_dom d₂)
      (r₂ : internal_cat_cod d₁ · p = q · internal_cat_cod d₂)
  : PullbackPr1 (PB _ _ _ (internal_cat_cod d₁) (internal_cat_dom d₁))
    · q · internal_cat_cod d₂
    =
    PullbackPr2 (PB _ _ _ (internal_cat_cod d₁) (internal_cat_dom d₁))
    · q · internal_cat_dom d₂.
Proof.
  rewrite !assoc'.
  rewrite <- r₁, <- r₂.
  rewrite !assoc.
  apply maponpaths_2.
  exact (PullbackSqrCommutes (PB _ _ _ (internal_cat_cod d₁) (internal_cat_dom d₁))).
Qed.

Definition path_of_internal_cat_data
           {C : category}
           {PB : Pullbacks C}
           (d₁ d₂ : internal_cat_data PB)
  : UU
  := ∑ (p : path_of_internal_cat_diag d₁ d₂),
     (internal_cat_id d₁ · idtoiso (path_of_internal_cat_diag_mor p)
      =
      idtoiso (path_of_internal_cat_diag_ob p) · internal_cat_id d₂)
     ×
     (internal_cat_comp d₁ · idtoiso (path_of_internal_cat_diag_mor p)
      =
      PullbackArrow
        _ _ _ _
        (internal_cat_eq_comp
           (path_of_internal_cat_diag_dom p)
           (path_of_internal_cat_diag_cod p))
      · internal_cat_comp d₂).

Coercion path_of_internal_cat_data_to_diag
         {C : category}
         {PB : Pullbacks C}
         {d₁ d₂ : internal_cat_data PB}
         (p : path_of_internal_cat_data d₁ d₂)
  : path_of_internal_cat_diag d₁ d₂
  := pr1 p.

Proposition path_of_internal_cat_data_id
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat_data PB}
            (p : path_of_internal_cat_data d₁ d₂)
  : internal_cat_id d₁ · idtoiso (path_of_internal_cat_diag_mor p)
    =
    idtoiso (path_of_internal_cat_diag_ob p) · internal_cat_id d₂.
Proof.
  exact (pr12 p).
Qed.

Proposition path_of_internal_cat_data_comp
            {C : category}
            {PB : Pullbacks C}
            {d₁ d₂ : internal_cat_data PB}
            (p : path_of_internal_cat_data d₁ d₂)
  : internal_cat_comp d₁ · idtoiso (path_of_internal_cat_diag_mor p)
    =
    PullbackArrow
      _ _ _ _
      (internal_cat_eq_comp
         (path_of_internal_cat_diag_dom p)
         (path_of_internal_cat_diag_cod p))
    · internal_cat_comp d₂.
Proof.
  exact (pr22 p).
Qed.

Definition internal_cat_data_eq
           {C : category}
           {PB : Pullbacks C}
           (d₁ d₂ : internal_cat_data PB)
  : (d₁ = d₂) ≃ path_of_internal_cat_data d₁ d₂.
Proof.
  induction d₁ as [ d₁ H₁ ].
  induction d₂ as [ d₂ H₂ ].
  refine (_ ∘ total2_paths_equiv _ _ _)%weq.
  refine (weqtotal2 (internal_cat_diag_eq d₁ d₂) _).
  intro p ; cbn in p.
  induction p.
  refine (_ ∘ pathsdirprodweq)%weq.
  use weqdirprodf.
  - cbn.
    rewrite id_left, id_right.
    refine (path_sigma_hprop _ _ _ _)%weq.
    apply isapropdirprod ; apply homset_property.
  - refine (_ ∘ path_sigma_hprop _ _ _ _)%weq.
    {
      apply isapropdirprod ; apply homset_property.
    }
    induction H₁ as [ i₁ [ c₁ H₁ ] ].
    induction H₂ as [ i₂ [ c₂ H₂ ] ].
    rewrite id_right ; cbn.
    use weqimplimpl.
    + intro p.
      refine (p @ !(id_left _) @ _).
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      * rewrite id_left, id_right.
        apply idpath.
      * rewrite id_left, id_right.
        apply idpath.
    + intro p.
      refine (p @ !_ @ id_left _).
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      * rewrite id_left, id_right.
        apply idpath.
      * rewrite id_left, id_right.
        apply idpath.
    + apply homset_property.
    + apply homset_property.
Defined.

Definition internal_cat_eq
           {C : category}
           {PB : Pullbacks C}
           (d₁ d₂ : internal_cat PB)
  : (d₁ = d₂) ≃ path_of_internal_cat_data d₁ d₂.
Proof.
  refine (internal_cat_data_eq d₁ d₂ ∘ path_sigma_hprop _ _ _ _)%weq.
  apply isaprop_disp_cat_axioms.
Defined.

(** * 3. Isomorphisms of internal categories *)
Section InternalCatEqIso.
  Context {C : category}
          (H : is_univalent C)
          {PB : Pullbacks C}
          (d₁ d₂ : internal_cat PB).

  Definition internal_cat_eq_z_iso_mor
             (p : path_of_internal_cat_data d₁ d₂)
    : ∑ (p : z_iso (internal_cat_ob d₁) (internal_cat_ob d₂))
        (q : z_iso (internal_cat_mor d₁) (internal_cat_mor d₂))
        (r₁ : internal_cat_dom d₁ · p = q · internal_cat_dom d₂)
        (r₂ : internal_cat_cod d₁ · p = q · internal_cat_cod d₂),
      (internal_cat_id d₁ · q = p · internal_cat_id d₂)
      ×
      (internal_cat_comp d₁ · q
       =
       PullbackArrow _ _ _ _ (internal_cat_eq_comp r₁ r₂)
       · internal_cat_comp d₂).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact (idtoiso (path_of_internal_cat_diag_ob p)).
    - exact (idtoiso (path_of_internal_cat_diag_mor p)).
    - exact (path_of_internal_cat_diag_dom p).
    - exact (path_of_internal_cat_diag_cod p).
    - exact (path_of_internal_cat_data_id p).
    - exact (path_of_internal_cat_data_comp p).
  Defined.

  Definition internal_cat_eq_z_iso_inv
    : (∑ (p : z_iso (internal_cat_ob d₁) (internal_cat_ob d₂))
         (q : z_iso (internal_cat_mor d₁) (internal_cat_mor d₂))
         (r₁ : internal_cat_dom d₁ · p = q · internal_cat_dom d₂)
         (r₂ : internal_cat_cod d₁ · p = q · internal_cat_cod d₂),
       (internal_cat_id d₁ · q = p · internal_cat_id d₂)
       ×
       (internal_cat_comp d₁ · q
        =
        PullbackArrow _ _ _ _ (internal_cat_eq_comp r₁ r₂)
          · internal_cat_comp d₂))
      → path_of_internal_cat_data d₁ d₂.
  Proof.
    intros (p & q & r₁ & r₂ & s₁ & s₂).
    simple refine ((_ ,, _ ,, _ ,, _) ,, _ ,, _).
    - exact (isotoid _ H p).
    - exact (isotoid _ H q).
    - abstract
        (rewrite !idtoiso_isotoid ;
         apply r₁).
    - cbn.
      abstract
        (rewrite !idtoiso_isotoid ;
         apply r₂).
    - cbn.
      abstract
        (rewrite !idtoiso_isotoid ;
         apply s₁).
    - abstract
        (cbn ;
         etrans ;
         [ apply maponpaths ;
           exact (maponpaths pr1 (idtoiso_isotoid _ H _ _ q))
         | ] ;
         refine (s₂ @ _) ;
         apply maponpaths_2 ;
         use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))) ;
         [ rewrite PullbackArrow_PullbackPr1 ;
           rewrite !idtoiso_isotoid ;
           apply idpath
         | rewrite PullbackArrow_PullbackPr2 ;
           rewrite !idtoiso_isotoid ;
           apply idpath ]).
  Defined.

  Proposition internal_cat_eq_z_iso_left
              (p : path_of_internal_cat_data d₁ d₂)
    : internal_cat_eq_z_iso_inv (internal_cat_eq_z_iso_mor p) = p.
  Proof.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    use total2_paths_f.
    - apply isotoid_idtoiso.
    - use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      rewrite pr1_transportf.
      rewrite transportf_const.
      cbn.
      apply isotoid_idtoiso.
  Qed.

  Proposition internal_cat_eq_z_iso_right
              p
    : internal_cat_eq_z_iso_mor (internal_cat_eq_z_iso_inv p) = p.
  Proof.
    use total2_paths_f.
    - apply idtoiso_isotoid.
    - use subtypePath.
      + intro.
        use isaproptotal2.
        * intro.
          use isaproptotal2.
          ** intro.
             apply isapropdirprod ; apply homset_property.
          ** intros.
             apply homset_property.
        * intros.
          apply homset_property.
      + rewrite pr1_transportf.
        rewrite transportf_const.
        apply idtoiso_isotoid.
  Qed.
          
  Definition internal_cat_eq_z_iso
    : (d₁ = d₂)
      ≃
      (∑ (p : z_iso (internal_cat_ob d₁) (internal_cat_ob d₂))
         (q : z_iso (internal_cat_mor d₁) (internal_cat_mor d₂))
         (r₁ : internal_cat_dom d₁ · p = q · internal_cat_dom d₂)
         (r₂ : internal_cat_cod d₁ · p = q · internal_cat_cod d₂),
       (internal_cat_id d₁ · q = p · internal_cat_id d₂)
       ×
       (internal_cat_comp d₁ · q
        =
        PullbackArrow _ _ _ _ (internal_cat_eq_comp r₁ r₂)
        · internal_cat_comp d₂)).
  Proof.
    refine (_ ∘ internal_cat_eq d₁ d₂)%weq.
    use weq_iso.
    - exact internal_cat_eq_z_iso_mor.
    - exact internal_cat_eq_z_iso_inv.
    - exact internal_cat_eq_z_iso_left.
    - exact internal_cat_eq_z_iso_right.
  Defined.
End InternalCatEqIso.

Section InternalCatIso.
  Context {C : category}
          {PB : Pullbacks C}
          {d₁ d₂ : internal_cat PB}
          (p : z_iso (internal_cat_ob d₁) (internal_cat_ob d₂))
          (q : z_iso (internal_cat_mor d₁) (internal_cat_mor d₂))
          (r₁ : internal_cat_dom d₁ · p = q · internal_cat_dom d₂)
          (r₂ : internal_cat_cod d₁ · p = q · internal_cat_cod d₂)
          (s₁ : internal_cat_id d₁ · q = p · internal_cat_id d₂)
          (s₂ : internal_cat_comp d₁ · q
                =
                PullbackArrow _ _ _ _ (internal_cat_eq_comp r₁ r₂)
                · internal_cat_comp d₂).
  
  Definition make_internal_cat_iso_mor_data
    : internal_functor_data d₁ d₂.
  Proof.
    use make_internal_functor_data.
    - split.
      + exact p.
      + exact q.
    - exact (!r₁).
    - exact (!r₂).
  Defined.

  Proposition make_internal_cat_iso_mor_axioms
    : disp_functor_axioms
        (internal_functor_to_disp_functor_data
           make_internal_cat_iso_mor_data).
  Proof.
    use make_internal_functor_axioms.
    - intros Γ x.
      use internal_morphism_eq ; cbn.
      rewrite !assoc'.
      apply maponpaths.
      exact s₁.
    - intros Γ x₁ x₂ x₃ g₁ g₂.
      use internal_morphism_eq ; cbn.
      rewrite !assoc'.
      rewrite s₂.
      rewrite !assoc.
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      + rewrite assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
  Qed.
  
  Definition make_internal_cat_iso_mor
    : internal_functor d₁ d₂.
  Proof.
    use make_internal_functor.
    - exact make_internal_cat_iso_mor_data.
    - exact make_internal_cat_iso_mor_axioms.
  Defined.

  Definition make_internal_cat_iso_inv_data
    : internal_functor_data d₂ d₁.
  Proof.
    use make_internal_functor_data.
    - split.
      + exact (inv_from_z_iso p).
      + exact (inv_from_z_iso q).
    - abstract
        (cbn ;
         use z_iso_inv_on_right ;
         rewrite !assoc ;
         use z_iso_inv_on_left ;
         exact (!r₁)).
    - abstract
        (cbn ;
         use z_iso_inv_on_right ;
         rewrite !assoc ;
         use z_iso_inv_on_left ;
         exact (!r₂)).
  Defined.

  Proposition make_internal_cat_iso_inv_axioms
    : disp_functor_axioms
        (internal_functor_to_disp_functor_data
           make_internal_cat_iso_inv_data).
  Proof.
    use make_internal_functor_axioms.
    - intros Γ x.
      use internal_morphism_eq ; cbn.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      use z_iso_inv_on_right.
      rewrite !assoc.
      use z_iso_inv_on_left.
      exact (!s₁).
    - intros Γ x₁ x₂ x₃ g₁ g₂.
      use internal_morphism_eq ; cbn.
      refine (!_).
      use z_iso_inv_on_left.
      rewrite !assoc'.
      rewrite s₂.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      + rewrite assoc'.
        rewrite PullbackArrow_PullbackPr1.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr1.
        rewrite !assoc'.
        rewrite z_iso_after_z_iso_inv.
        apply id_right.
      + rewrite assoc'.
        rewrite PullbackArrow_PullbackPr2.
        rewrite assoc.
        rewrite PullbackArrow_PullbackPr2.
        rewrite !assoc'.
        rewrite z_iso_after_z_iso_inv.
        apply id_right.
  Qed.
  
  Definition make_internal_cat_iso_inv
    : internal_functor d₂ d₁.
  Proof.
    use make_internal_functor.
    - exact make_internal_cat_iso_inv_data.
    - exact make_internal_cat_iso_inv_axioms.
  Defined.

  Proposition make_internal_cat_iso_eqs
    : is_inverse_in_precat
        (C := cat_of_internal_cat PB)
        make_internal_cat_iso_mor
        make_internal_cat_iso_inv.
  Proof.
    split.
    - use internal_functor_eq ; cbn.
      + apply z_iso_inv_after_z_iso.
      + apply z_iso_inv_after_z_iso.
    - use internal_functor_eq ; cbn.
      + apply z_iso_after_z_iso_inv.
      + apply z_iso_after_z_iso_inv.
  Qed.
  
  Definition make_internal_cat_iso
    : z_iso (C := cat_of_internal_cat PB) d₁ d₂.
  Proof.
    use make_z_iso.
    - exact make_internal_cat_iso_mor.
    - exact make_internal_cat_iso_inv.
    - exact make_internal_cat_iso_eqs.
  Defined.
End InternalCatIso.

Section InternalCatIsoWeq.
  Context {C : category}
          {PB : Pullbacks C}
          (d₁ d₂ : internal_cat PB).

  Section FromIso.
    Context (f : z_iso (C := cat_of_internal_cat PB) d₁ d₂).

    Let g : internal_functor d₁ d₂ := pr1 f.
    Let h : internal_functor d₂ d₁ := inv_from_z_iso f.
    
    Definition internal_cat_z_iso_to_path_ob
      : z_iso (internal_cat_ob d₁) (internal_cat_ob d₂).
    Proof.
      use make_z_iso.
      - exact (internal_functor_ob g).
      - exact (internal_functor_ob h).
      - abstract
          (split ;
           [ exact (maponpaths (λ z, pr111 z) (z_iso_inv_after_z_iso f))
           | exact (maponpaths (λ z, pr111 z) (z_iso_after_z_iso_inv f)) ]).
    Defined.
    
    Definition internal_cat_z_iso_to_path_mor
      : z_iso (internal_cat_mor d₁) (internal_cat_mor d₂).
    Proof.
      use make_z_iso.
      - exact (internal_functor_mor g).
      - exact (internal_functor_mor h).
      - abstract
          (split ;
           [ exact (maponpaths (λ z, dirprod_pr2 (pr11 z)) (z_iso_inv_after_z_iso f))
           | exact (maponpaths (λ z, dirprod_pr2 (pr11 z)) (z_iso_after_z_iso_inv f)) ]).
    Defined.

    Proposition internal_cat_z_iso_to_path_lem
      : internal_cat_comp d₁ · internal_functor_mor g
        =
        PullbackArrow
          _ _ _ _
          (internal_cat_eq_comp
             (!(internal_functor_mor_dom g))
             (!(internal_functor_mor_cod g)))
        · internal_cat_comp d₂.
    Proof.
      pose (maponpaths
              pr1
              (internal_functor_comp
                 g
                 (internal_cat_composable_left_mor d₁)
                 (internal_cat_composable_right_mor d₁)))
        as p.
      cbn in p.
      refine (_ @ p @ _).
      - refine (!(id_left _) @ _).
        rewrite !assoc.
        do 2 apply maponpaths_2.
        use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
        + apply id_left.
        + apply id_left.
      - apply maponpaths_2.
        use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
        + apply PullbackArrow_PullbackPr1.
        + apply PullbackArrow_PullbackPr2.
    Qed.
    
    Definition internal_cat_z_iso_to_path             
      : ∑ (p : z_iso (internal_cat_ob d₁) (internal_cat_ob d₂))
          (q : z_iso (internal_cat_mor d₁) (internal_cat_mor d₂))
          (r₁ : internal_cat_dom d₁ · p = q · internal_cat_dom d₂)
          (r₂ : internal_cat_cod d₁ · p = q · internal_cat_cod d₂),
        (internal_cat_id d₁ · q = p · internal_cat_id d₂)
        ×
        (internal_cat_comp d₁ · q
         =
         PullbackArrow _ _ _ _ (internal_cat_eq_comp r₁ r₂)
         · internal_cat_comp d₂).
    Proof.
      simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _).
      - exact internal_cat_z_iso_to_path_ob.
      - exact internal_cat_z_iso_to_path_mor.
      - cbn.
        refine (!_).
        apply internal_functor_mor_dom.
      - cbn.
        refine (!_).
        apply internal_functor_mor_cod.
      - abstract
          (cbn ;
           refine (_ @ maponpaths pr1 (internal_functor_id g (identity _)) @ _) ;
           cbn ;
           rewrite id_left ;
           apply idpath).
      - apply internal_cat_z_iso_to_path_lem.
    Defined.
  End FromIso.
    
  Definition internal_cat_z_iso_weq
    : (∑ (p : z_iso (internal_cat_ob d₁) (internal_cat_ob d₂))
         (q : z_iso (internal_cat_mor d₁) (internal_cat_mor d₂))
         (r₁ : internal_cat_dom d₁ · p = q · internal_cat_dom d₂)
         (r₂ : internal_cat_cod d₁ · p = q · internal_cat_cod d₂),
       (internal_cat_id d₁ · q = p · internal_cat_id d₂)
       ×
       (internal_cat_comp d₁ · q
        =
        PullbackArrow _ _ _ _ (internal_cat_eq_comp r₁ r₂)
        · internal_cat_comp d₂))
      ≃
      z_iso (C := cat_of_internal_cat PB) d₁ d₂.
  Proof.
    use weq_iso.
    - intros (p & q & r₁ & r₂ & s₁ & s₂).
      exact (make_internal_cat_iso p q r₁ r₂ s₁ s₂).
    - exact internal_cat_z_iso_to_path.
    - abstract
        (intro p ; cbn ;
         use total2_paths_f ;
         [ use z_iso_eq ; cbn ;
           apply idpath | ] ;
         use subtypePath ;
         [ intro ;
           use isaproptotal2 ;
           [ intro ;
             use isaproptotal2 ;
             [ intro ;
               apply isapropdirprod ; apply homset_property
             | intros ;
               apply homset_property ]
           | intros ;
             apply homset_property ]
         | ] ;
         rewrite pr1_transportf ;
         rewrite transportf_const ;
         use z_iso_eq ; cbn ;
         apply idpath).
    - abstract
        (intro f ;
         use z_iso_eq ;
         use internal_functor_eq ;
         cbn ;
         apply idpath).
  Defined.
End InternalCatIsoWeq.

(** * 4. The category of internal categories is univalent *)
Proposition is_univalent_internal_cat
            {C : category}
            (H : is_univalent C)
            (PB : Pullbacks C)
  : is_univalent (cat_of_internal_cat PB).
Proof.
  intros d₁ d₂.
  use weqhomot.
  - exact (internal_cat_z_iso_weq d₁ d₂ ∘ internal_cat_eq_z_iso H d₁ d₂)%weq.
  - intro p.
    induction p.
    use z_iso_eq.
    use internal_functor_eq.
    + apply idpath.
    + apply idpath.
Qed.

Definition univalent_cat_of_internal_cat
            {C : category}
            (H : is_univalent C)
            (PB : Pullbacks C)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (cat_of_internal_cat PB).
  - exact (is_univalent_internal_cat H PB).
Defined.
