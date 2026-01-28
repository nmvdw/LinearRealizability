(**

 Equivalence between PERs and modest sets

 We show that the categories of PERs and modest sets are equivalent.

 Contents
 1. Every PER gives rise to a modest set
 2. Morphisms of PERs give morphisms of modest sets
 3. The functor from PERs to modest sets
 4. Modest sets to PERs
 5. Morphisms of modest sets give rise to morphisms of PERs
 6. Fullness and faithfulness
 7. Equivalence between PERs and modest sets

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.ModestSet.
Require Import Assemblies.PartialEqRel.

Local Open Scope bi.
Local Open Scope assembly.
Local Open Scope cat.

(** * 1. Every PER gives rise to a modest set *)
Definition per_to_assembly_rel
           {A : bi_algebra}
           (R : ca_per A)
           (a : A)
  : dom_ca_per_quot R → hProp.
Proof.
  use (setquotuniv _ hPropset).
  - exact (λ (x : dom_ca_per R), R a x).
  - abstract
      (intros x₁ x₂ ;
       apply ca_per_weq_left).
Defined.

Definition per_to_assembly
           {A : bi_algebra}
           (R : ca_per A)
  : assembly A.
Proof.
  use make_assembly'.
  - exact (dom_ca_per_quot R).
  - exact (per_to_assembly_rel R).
  - abstract
      (use setquotunivprop' ; [ intro ; apply propproperty | ] ;
       intro x ;
       use hinhpr ; cbn ;
       refine (dom_ca_per_el x ,, _) ;
       apply dom_ca_per_refl).
Defined.

Definition per_to_modest_set
           {A : bi_algebra}
           (R : ca_per A)
  : modest_set A.
Proof.
  use make_modest_set.
  - exact (per_to_assembly R).
  - abstract
      (intros a ;
       use setquotunivprop' ; [ intro ; apply propproperty | ] ;
       intro x₁ ;
       use setquotunivprop' ; [ intro ; apply propproperty | ] ;
       intros x₂ p₁ p₂ ;
       use iscompsetquotpr ;
       cbn in * ;
       refine (istrans_ca_per _ _ p₂) ;
       exact (issymm_ca_per _ p₁)).
Defined.

Proposition per_to_modest_set_trans
            {A : bi_algebra}
            (R : ca_per A)
            {a₁ a₂ : A}
  : ∏ (z : per_to_modest_set R), a₁ ⊩ z → a₂ ⊩ z → R a₁ a₂.
Proof.
  use setquotunivprop'.
  {
    intro.
    do 2 (use impred ; intro).
    apply propproperty.
  }
  cbn ; intros x p₁ p₂.
  refine (istrans_ca_per _ p₁ _).
  exact (issymm_ca_per _ p₂).
Qed.
      
(** * 2. Morphisms of PERs give morphisms of modest sets *)
Definition per_to_modest_set_morphism
           {A : bi_algebra}
           {R₁ R₂ : ca_per A}
           (φ : ca_per_morphism R₁ R₂)
  : modest_set_morphism
      (per_to_modest_set R₁)
      (per_to_modest_set R₂).
Proof.
  use make_modest_set_morphism.
  use make_assembly_morphism.
  - exact (ca_per_morphism_function φ).
  - abstract
      (revert φ ;
       use setquotunivprop ;
       intro a ;
       use hinhpr ;
       refine (pr1 a ,, _) ;
       intro b ;
       use setquotunivprop ;
       intros b' p ; cbn ;
       use ca_per_tracker_map_related ;
       exact p).
Defined.

(** * 3. The functor from PERs to modest sets *)
Definition ca_per_to_modest_set_functor_data
           (A : bi_algebra)
  : functor_data
      (cat_of_ca_pers A)
      (cat_of_modest_set A).
Proof.
  use make_functor_data.
  - exact per_to_modest_set.
  - exact (λ _ _ φ, per_to_modest_set_morphism φ).
Defined.

Proposition ca_per_to_modest_set_functor_laws
            (A : bi_algebra)
  : is_functor (ca_per_to_modest_set_functor_data A).
Proof.
  split.
  - intro R.
    use eq_modest_set_morphism.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intro x.
    use iscompsetquotpr ; cbn.
    rewrite bi_algebra_i_eq.
    apply dom_ca_per_refl.
  - intros R₁ R₂ R₃.
    use setquotunivprop' ; [ intro ; use impred ; intro ; apply homset_property | ].
    intro a₁.
    use setquotunivprop' ; [ intro ; apply homset_property | ].
    intro a₂.
    use eq_modest_set_morphism.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intro b.
    use iscompsetquotpr ; cbn.
    rewrite bi_algebra_b_eq.
    apply (ca_per_tracker_map_related a₂).
    apply (ca_per_tracker_map_related a₁).
    apply dom_ca_per_refl.
Qed.

Definition ca_per_to_modest_set_functor
           (A : bi_algebra)
  : cat_of_ca_pers A ⟶ cat_of_modest_set A.
Proof.
  use make_functor.
  - exact (ca_per_to_modest_set_functor_data A).
  - exact (ca_per_to_modest_set_functor_laws A).
Defined.

(** * 4. Modest sets to PERs *)
Definition modest_set_to_per_hrel
           {A : bi_algebra}
           (X : modest_set A)
  : hrel A.
Proof.
  intros a₁ a₂.
  use make_hProp.
  - exact (∑ (x : X), a₁ ⊩ x ∧ a₂ ⊩ x).
  - abstract
      (use isaproptotal2 ; [ intro ; apply propproperty | ] ;
       intros x₁ x₂ [ p₁ p₂ ] [ q₁ q₂ ] ;
       exact (is_modest_modest_set X p₁ q₁)).
Defined.

Definition modest_set_to_per
           {A : bi_algebra}
           (X : modest_set A)
  : ca_per A.
Proof.
  use make_ca_per.
  - exact (modest_set_to_per_hrel X).
  - abstract
      (intros a₁ a₂ ( x & p₁ & p₂ ) ;
       exact (x ,, p₂ ,, p₁)).
  - abstract
      (intros a₁ a₂ a₃ ( x & p₁ & p₂ ) ( y & q₁ & q₂ ) ;
       pose proof (is_modest_modest_set X p₂ q₁) as r ;
       induction r ;
       exact (x ,, p₁ ,, q₂)).
Defined.

Definition modest_set_to_per_z_iso_mor
           {A : bi_algebra}
           (X : modest_set A)
  : modest_set_morphism
      (per_to_modest_set (modest_set_to_per X))
      X.
Proof.
  use make_modest_set_morphism.
  use make_assembly_morphism.
  - use setquotuniv.
    + exact (λ x, pr12 x).
    + abstract
        (intros ( a₁ & x₁ & p₁ & q₁ ) ( a₂ & x₂ & p₂ & q₂ ) ( y & r₁ & r₂ ) ;
         cbn in r₁, r₂ ; cbn ;
         refine (is_modest_modest_set X p₁ r₁ @ !_) ;
         exact (is_modest_modest_set X p₂ r₂)).
  - abstract
      (use hinhpr ;
       refine (I ,, _) ;
       intros b ;
       use setquotunivprop' ; [ intro ; apply propproperty | ] ;
       intros ( x & p ) q ; cbn ;
       cbn in p, q ;
       rewrite bi_algebra_i_eq ;
       rewrite (is_modest_modest_set X (pr12 p) (pr22 q)) ;
       exact (pr12 q)).
Defined.

Definition unique_fiber_modest_set_to_per_el
           {A : bi_algebra}
           {X : modest_set A}
           (x : X)
           {a : A}
           (p : a ⊩ x)
  : ∑ b, modest_set_to_per_z_iso_mor X b = x.
Proof.
  simple refine (_ ,, _).
  - use setquotpr.
    use make_dom_ca_per.
    + exact a.
    + exact (x ,, p ,, p).
  - apply idpath.
Defined.

Proposition isaprop_fiber_modest_set_to_per
            {A : bi_algebra}
            {X : modest_set A}
            (x : X)
  : isaprop (∑ b, modest_set_to_per_z_iso_mor X b = x).
Proof.
  use invproofirrelevance.
  intros b₁ b₂.
  use subtypePath.
  {
    intro.
    apply setproperty.
  }
  induction b₁ as [ b₁ q₁ ].
  revert b₁ q₁.
  use setquotunivprop'.
  {
    intro.
    use impred ; intro.
    apply setproperty.
  }
  intros (b₁ & y₁ & q₁) r₁.
  induction b₂ as [ b₂ q₂ ].
  revert b₂ q₂.
  use setquotunivprop'.
  {
    intro.
    use impred ; intro.
    apply setproperty.
  }
  intros (b₂ & y₂ & q₂) r₂.
  use iscompsetquotpr ; cbn ; cbn in r₁, r₂.
  induction r₁, r₂.
  exact (y₂ ,, pr1 q₁ ,, pr1 q₂).
Qed.

Proposition unique_fiber_modest_set_to_per
            {A : bi_algebra}
            {X : modest_set A}
            (x : X)
  : ∃! a, modest_set_to_per_z_iso_mor X a = x.
Proof.
  pose proof (assembly_realizes_el x) as p.
  revert p.
  use factor_through_squash.
  {
    apply isapropiscontr.
  }
  intros (a & p).
  use iscontraprop1.
  - exact (isaprop_fiber_modest_set_to_per x).
  - exact (unique_fiber_modest_set_to_per_el x p).
Qed.

Proposition modest_set_to_per_z_iso_inv_tracks
            {A : bi_algebra}
            (X : modest_set A)
  : ∃ (a : A), tracks_morphism a (λ (x : X), pr11 (unique_fiber_modest_set_to_per x)).
Proof.
  use hinhpr.
  refine (I ,, _).
  intros a x p.
  rewrite bi_algebra_i_eq.
  pose proof (assembly_realizes_el x) as q.
  revert q.
  use factor_through_squash_hProp.
  intros (b & q).
  assert (pr11 (unique_fiber_modest_set_to_per x)
          =
          pr1 (unique_fiber_modest_set_to_per_el x p))
    as r.
  {
    apply (maponpaths pr1 (proofirrelevance _ (isaprop_fiber_modest_set_to_per x) _ _)).
  }
  rewrite r.
  cbn.
  exact (x ,, p ,, p).
Qed.

Definition modest_set_to_per_z_iso_inv
           {A : bi_algebra}
           (X : modest_set A)
  : modest_set_morphism
      X
      (per_to_modest_set (modest_set_to_per X)).
Proof.
  use make_modest_set_morphism.
  use make_assembly_morphism.
  - intro x.
    exact (pr11 (unique_fiber_modest_set_to_per x)).
  - exact (modest_set_to_per_z_iso_inv_tracks X).
Defined.

Proposition modest_set_to_per_z_iso_laws
            {A : bi_algebra}
            (X : modest_set A)
  : is_inverse_in_precat
      (modest_set_to_per_z_iso_mor X)
      (modest_set_to_per_z_iso_inv X).
Proof.
  split.
  - use eq_modest_set_morphism.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros ( a & x & p₁ & p₂ ).
    pose proof (assembly_realizes_el x) as q.
    revert q.
    use factor_through_squash.
    {
      apply setproperty.
    }
    intros ( b & q ).
    assert (pr11 (unique_fiber_modest_set_to_per x)
            =
            pr1 (unique_fiber_modest_set_to_per_el x q))
      as r.
    {
      apply (maponpaths pr1 (proofirrelevance _ (isaprop_fiber_modest_set_to_per x) _ _)).
    }
    cbn.
    rewrite r.
    use (iscompsetquotpr (dom_ca_per_quot_eqrel (modest_set_to_per X))).
    cbn.
    exact (x ,, q ,, p₁).
  - use eq_modest_set_morphism.
    intro x.
    exact (pr21 (unique_fiber_modest_set_to_per x)).
Qed.

Definition modest_set_to_per_z_iso
           {A : bi_algebra}
           (X : modest_set A)
  : z_iso (per_to_modest_set (modest_set_to_per X)) X.
Proof.
  use make_z_iso.
  - exact (modest_set_to_per_z_iso_mor X).
  - exact (modest_set_to_per_z_iso_inv X).
  - exact (modest_set_to_per_z_iso_laws X).
Defined.

Definition split_essentially_surjective_ca_per_to_modest_set_functor
           (A : bi_algebra)
  : split_essentially_surjective (ca_per_to_modest_set_functor A).
Proof.
  intros X.
  refine (modest_set_to_per X ,, _).
  exact (modest_set_to_per_z_iso X).
Defined.

(** * 6. Fullness and faithfulness *)
Section Fullness.
  Context {A : bi_algebra}
          {R₁ R₂ : ca_per A}
          (f : modest_set_morphism
                 (per_to_modest_set R₁)
                 (per_to_modest_set R₂))
          {a : A}
          (Ha : tracks_morphism a f).

  Lemma tracks_morphism_rel
        {b₁ b₂ : A}
        (p : R₁ b₁ b₂)
    :  R₂ (a · b₁)%bi (a · b₂)%bi.
  Proof.
    pose (refl_l_ca_per p) as q₁.
    pose (x₁ := make_dom_ca_per b₁ q₁).
    pose (y₁ := setquotpr (dom_ca_per_quot_eqrel R₁) x₁).
    pose proof (Ha b₁ y₁ q₁) as Hf₁.
    pose (refl_r_ca_per p) as q₂.
    pose (x₂ := make_dom_ca_per b₂ q₂).
    pose (y₂ := setquotpr (dom_ca_per_quot_eqrel R₁) x₂).
    pose proof (Ha b₂ y₁ (issymm_ca_per _ p)) as Hf₂.
    exact (per_to_modest_set_trans _ _ Hf₁ Hf₂).
  Qed.
  
  Definition full_ca_per_to_modest_set_functor_mor
    : ca_per_morphism R₁ R₂.
  Proof.
    use setquotpr.
    refine (a ,, _).
    abstract
      (intros b₁ b₂ p ;
       use tracks_morphism_rel ;
       exact p).
  Defined.

  Proposition full_ca_per_to_modest_set_functor_eq
    : per_to_modest_set_morphism full_ca_per_to_modest_set_functor_mor
      =
      f.
  Proof.
    use eq_modest_set_morphism.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intro x.
    use is_modest_modest_set.
    - exact (a · x)%bi.
    - use tracks_morphism_rel ; cbn.
      apply dom_ca_per_refl.
    - exact (Ha x (setquotpr _ x) (dom_ca_per_refl x)).
  Qed.
End Fullness.

Proposition full_ca_per_to_modest_set_functor
            (A : bi_algebra)
  : full (ca_per_to_modest_set_functor A).
Proof.
  refine (λ (R₁ R₂ : ca_per A)
            (f : modest_set_morphism (per_to_modest_set R₁) (per_to_modest_set R₂)),
          _).
  pose proof (assembly_morphism_tracked f) as q.
  revert q.
  use factor_through_squash_hProp.
  intros ( a & Ha ).
  use hinhpr.
  simple refine (_ ,, _).
  - exact (full_ca_per_to_modest_set_functor_mor f Ha).
  - exact (full_ca_per_to_modest_set_functor_eq f Ha).
Qed.

Proposition faithful_ca_per_to_modest_set_functor
            (A : bi_algebra)
  : faithful (ca_per_to_modest_set_functor A).
Proof.
  refine (λ (R₁ R₂ : ca_per A)
            (f : modest_set_morphism (per_to_modest_set R₁) (per_to_modest_set R₂)),
          _).
  use invproofirrelevance.
  intros [ φ₁ p₁ ] [ φ₂ p₂ ].
  use subtypePath ; [ intro ; apply homset_property | ].
  revert φ₁ φ₂ p₁ p₂.
  use setquotunivprop'.
  {
    intro.
    repeat (use impred ; intro).
    apply setproperty.
  }
  intros a₁.
  use setquotunivprop'.
  {
    intro.
    repeat (use impred ; intro).
    apply setproperty.
  }
  intros a₂ p₁ p₂.
  use iscompsetquotpr ; cbn.
  intros b q.
  pose (p := eq_modest_set_morphism_point (p₁ @ !p₂) (setquotpr _ (b ,, q))).
  exact (invmap (weqpathsinsetquot _ _ _) p).
Qed.    

Proposition fully_faithful_ca_per_to_modest_set_functor
            (A : bi_algebra)
  : fully_faithful (ca_per_to_modest_set_functor A).
Proof.
  use full_and_faithful_implies_fully_faithful.
  split.
  - exact (full_ca_per_to_modest_set_functor A).
  - exact (faithful_ca_per_to_modest_set_functor A).
Qed.

(** * 7. Equivalence between PERs and modest sets *)
Definition ca_per_modeset_set_equivalence
           (A : bi_algebra)
  : adj_equivalence_of_cats (ca_per_to_modest_set_functor A).
Proof.
  use rad_equivalence_of_cats'.
  - exact (fully_faithful_ca_per_to_modest_set_functor A).
  - exact (split_essentially_surjective_ca_per_to_modest_set_functor A).
Defined.  
