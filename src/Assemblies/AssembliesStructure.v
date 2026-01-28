(**

 Structure on the category of assemblies

 In this file, we construct various structure on the category of assemblies. 

 Contents
 1. Adjunction between the categories of sets and assemblies
 2. The terminal object
 3. Binary product of assemblies
 4. Equalizers of assemblies
 5. Pullbacks
 6. Initial assembly
 7. Binary coproducts of assemblies
 8. Natural numbers object of assemblies
 9. Exponentials
 10. Fibers

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.
Require Import UniMath.CategoryTheory.Exponentials.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

(** * 1. Adjunction between the categories of sets and assemblies *)
Definition forgetful_assembly_data
           (A : bi_algebra)
  : functor_data (cat_of_assembly A) SET.
Proof.
  use make_functor_data.
  - exact (λ (X : assembly A), (X : hSet)).
  - exact (λ (X₁ X₂ : assembly A)
             (f : assembly_morphism X₁ X₂),
            assembly_morphism_function f).
Defined.

Proposition forgetful_assembly_laws
            (A : bi_algebra)
  : is_functor (forgetful_assembly_data A).
Proof.
  split ; intro ; intros ; apply idpath.
Qed.

Definition forgetful_assembly
           (A : bi_algebra)
  : cat_of_assembly A ⟶ SET.
Proof.
  use make_functor.
  - exact (forgetful_assembly_data A).
  - exact (forgetful_assembly_laws A).
Defined.

Definition discrete_assembly
           (A : bi_algebra)
           (X : hSet)
  : assembly A.
Proof.
  use make_assembly.
  - exact X.
  - exact (λ _ _, htrue).
  - abstract
      (intros ;
       apply propproperty).
  - abstract
      (intro ;
       use hinhpr ;
       exact (I ,, tt)%bi).
Defined.

Definition morphism_to_discrete
           {A : bi_algebra}
           {X₁ : hSet}
           {X₂ : assembly A}
           (f : X₂ → X₁)
  : assembly_morphism X₂ (discrete_assembly A X₁).
Proof.
  use make_assembly_morphism.
  - exact f.
  - abstract
      (use hinhpr ;
       refine (I ,, _)%bi ;
       intros ? ? ? ; cbn ;
       exact tt).
Defined.
    
Definition coreflection_forgetful_assembly_data
           (A : bi_algebra)
           (X : hSet)
  : coreflection_data (X : SET) (forgetful_assembly A).
Proof.
  use make_coreflection_data.
  - exact (discrete_assembly A X).
  - exact (λ x, x).
Defined.

Definition coreflection_forgetful_assembly_laws
           (A : bi_algebra)
           (X : hSet)
  : is_coreflection (coreflection_forgetful_assembly_data A X).
Proof.
  intros f.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros g₁ g₂ ;
       use subtypePath ; [ intro ; apply homset_property | ] ;
       use assembly_morphism_eq ;
       intro x ;
       exact (eqtohomot (!(pr2 g₁) @ pr2 g₂) x)).
  - simple refine (_ ,, _).
    + exact (morphism_to_discrete (coreflection_data_arrow f)).
    + abstract
        (cbn ;
         apply idpath).
Defined.

Definition coreflection_forgetful_assembly
           (A : bi_algebra)
           (X : hSet)
  : coreflection (X : SET) (forgetful_assembly A).
Proof.
  use make_coreflection.
  - exact (coreflection_forgetful_assembly_data A X).
  - exact (coreflection_forgetful_assembly_laws A X).
Defined.

Definition is_left_adjoint_forgetful_assembly
           (A : bi_algebra)
  : is_left_adjoint (forgetful_assembly A).
Proof.
  use coreflections_to_is_left_adjoint.
  exact (λ (X : hSet), coreflection_forgetful_assembly A X).
Defined.

(** * 2. The terminal object *)
Definition terminal_assembly
           (A : bi_algebra)
  : assembly A
  := discrete_assembly A unitset.

Definition terminal_assembly_morphism
           {A : bi_algebra}
           (X : assembly A)
  : assembly_morphism X (terminal_assembly A).
Proof.
  use make_assembly_morphism.
  - exact (λ _, tt).
  - abstract
      (use hinhpr ;
       refine (I ,, _)%bi ;
       intros b w p ; cbn ;
       exact tt).
Defined.

Definition terminal_cat_of_assembly
           (A : bi_algebra)
  : Terminal (cat_of_assembly A).
Proof.
  use make_Terminal.
  - exact (terminal_assembly A).
  - intros X.
    use make_iscontr.
    + exact (terminal_assembly_morphism X).
    + abstract
        (intros ;
         use assembly_morphism_eq ;
         intro ;
         apply isapropunit).
Defined.

(** * 3. Binary product of assemblies *)
Definition prod_assembly
           {A : combinatory_algebra}
           (X₁ X₂ : assembly A)
  : assembly A.
Proof.
  use make_assembly.
  - exact (X₁ × X₂)%set.
  - exact (λ a xy, π₁ · a ⊩ pr1 xy ∧ π₂ · a ⊩ pr2 xy)%ca.
  - abstract
      (intros ;
       apply propproperty).
  - abstract
      (intros xy ;
       induction xy as [ x y ] ;
       pose proof (assembly_realizes_el x) as p ;
       revert p ;
       use factor_through_squash_hProp ;
       intros [ a₁ Ha₁ ] ;
       pose proof (assembly_realizes_el y) as p ;
       revert p ;
       use factor_through_squash_hProp ;
       intros [ a₂ Ha₂ ] ;
       use hinhpr ;
       refine (pair · a₁ · a₂ ,, _)%ca ; simpl ;
       rewrite combinatory_algebra_pr1_pair ;
       rewrite combinatory_algebra_pr2_pair ;
       exact (Ha₁ ,, Ha₂)).
Defined.

Definition pr1_assembly_morphism
           {A : combinatory_algebra}
           (X₁ X₂ : assembly A)
  : assembly_morphism (prod_assembly X₁ X₂) X₁.
Proof.
  use make_assembly_morphism.
  - exact pr1.
  - abstract
      (use hinhpr ;
       refine (π₁ ,, _) ; simpl ;
       intros a xy p ;
       exact (pr1 p)).
Defined.

Definition pr2_assembly_morphism
           {A : combinatory_algebra}
           (X₁ X₂ : assembly A)
  : assembly_morphism (prod_assembly X₁ X₂) X₂.
Proof.
  use make_assembly_morphism.
  - exact pr2.
  - abstract
      (use hinhpr ;
       refine (π₂ ,, _) ; simpl ;
       intros a xy p ;
       exact (pr2 p)).
Defined.

Definition pair_assembly_morphism
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism X₃ X₁)
           (g : assembly_morphism X₃ X₂)
  : assembly_morphism X₃ (prod_assembly X₁ X₂).
Proof.
  use make_assembly_morphism.
  - exact (λ w, f w ,, g w).
  - abstract
      (pose proof (assembly_morphism_tracked f) as p ;
       revert p ;
       use factor_through_squash_hProp ;
       intros [ a₁ Ha₁ ] ;
       pose proof (assembly_morphism_tracked g) as p ;
       revert p ;
       use factor_through_squash_hProp ;
       intros [ a₂ Ha₂ ] ;
       use hinhpr ;
       refine (pairf · a₁ · a₂ ,, _)%ca ;
       intros b w p ; simpl ;
       specialize (Ha₁ b w p) ;
       specialize (Ha₂ b w p) ;
       simpl in Ha₁, Ha₂ ;
       rewrite combinatory_algebra_pr1_pair_fun ;
       rewrite combinatory_algebra_pr2_pair_fun ;
       exact (Ha₁ ,, Ha₂)).
Defined.

Definition binproducts_cat_of_assembly
           (A : combinatory_algebra)
  : BinProducts (cat_of_assembly A).
Proof.
  intros X₁ X₂.
  use make_BinProduct.
  - exact (prod_assembly X₁ X₂).
  - exact (pr1_assembly_morphism X₁ X₂).
  - exact (pr2_assembly_morphism X₁ X₂).
  - intros X₃ f g.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros h₁ h₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use assembly_morphism_eq ;
         intro x ;
         pose (assembly_morphism_eq_point (pr12 h₁ @ !(pr12 h₂)) x) as p ;
         pose (assembly_morphism_eq_point (pr22 h₁ @ !(pr22 h₂)) x) as q ;
         exact (pathsdirprod p q)).
    + refine (pair_assembly_morphism f g ,, _).
      abstract
        (split ;
         use assembly_morphism_eq ;
         intro ;
         apply idpath).
Defined.
  
(** * 4. Equalizers of assemblies *)
Definition equalizer_assembly
           {A : combinatory_algebra}
           {X₁ X₂ : assembly A}
           (f g : assembly_morphism X₁ X₂)
  : assembly A.
Proof.
  use make_assembly.
  - use make_hSet.
    + exact (∑ (x : X₁), f x = g x).
    + abstract
        (use isaset_total2 ; [ apply setproperty | ] ;
         intro ;
         apply isasetaprop ;
         apply setproperty).
  - exact (λ a x, a ⊩ pr1 x).
  - abstract
      (intros ;
       apply propproperty).
  - abstract
      (intros ( x & p ) ;
       exact (assembly_realizes_el x)).
Defined.

Definition equalizer_assembly_arrow
           {A : combinatory_algebra}
           {X₁ X₂ : assembly A}
           (f g : assembly_morphism X₁ X₂)
  : assembly_morphism (equalizer_assembly f g) X₁.
Proof.
  use make_assembly_morphism.
  - exact pr1.
  - abstract
      (use hinhpr ;
       refine (I ,, _) ;
       intros b w p ;
       rewrite combinatory_algebra_i_eq ;
       exact p).
Defined.

Proposition equalizer_assembly_arrow_eq
            {A : combinatory_algebra}
            {X₁ X₂ : assembly A}
            (f g : assembly_morphism X₁ X₂)
  : comp_assembly_morphism
      (equalizer_assembly_arrow f g)
      f
    =
    comp_assembly_morphism
      (equalizer_assembly_arrow f g)
      g.
Proof.
  use assembly_morphism_eq.
  intro ; cbn.
  exact (pr2 x).
Qed.
  
Definition equalizer_assembly_in
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f g : assembly_morphism X₁ X₂)
           (h : assembly_morphism X₃ X₁)
           (p : comp_assembly_morphism h f = comp_assembly_morphism h g)
  : assembly_morphism X₃ (equalizer_assembly f g).
Proof.
  use make_assembly_morphism.
  - refine (λ x, h x ,, _).
    exact (assembly_morphism_eq_point p x).
  - abstract
      (pose proof (assembly_morphism_tracked h) as q ;
       revert q ;
       use factor_through_squash_hProp ;
       intros ( a & Ha ) ;
       use hinhpr ;
       refine (a ,, _) ;
       intros b w r ;
       simpl ;
       exact (Ha b w r)).
Defined.

Definition equalizers_cat_of_assembly
           (A : combinatory_algebra)
  : Equalizers (cat_of_assembly A).
Proof.
  intros X₁ X₂ f g.
  use make_Equalizer.
  - exact (equalizer_assembly f g).
  - exact (equalizer_assembly_arrow f g).
  - exact (equalizer_assembly_arrow_eq f g).
  - intros X₃ h p.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros k₁ k₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use assembly_morphism_eq ;
         intro x ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         exact (assembly_morphism_eq_point (pr2 k₁ @ !(pr2 k₂)) x)).
    + refine (equalizer_assembly_in f g h p ,, _).
      abstract
        (use assembly_morphism_eq ;
         intro ;
         apply idpath).
Defined.

(** * 5. Pullbacks *)
Definition pullback_assembly
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism X₁ X₃)
           (g : assembly_morphism X₂ X₃)
  : assembly A.
Proof.
  use make_assembly.
  - use make_hSet.
    + exact (∑ (x : X₁) (y : X₂), f x = g y).
    + abstract
        (use isaset_total2 ; [ apply setproperty | ] ;
         intro ;
         use isaset_total2 ; [ apply setproperty | ] ;
         intro ;
         apply isasetaprop ;         
         apply setproperty).
  - exact (λ a x, π₁ · a ⊩ pr1 x ∧ π₂ · a ⊩ pr12 x)%ca.
  - abstract
      (intros ;
       apply propproperty).
  - abstract
      (intros ( x & y & p ) ;
       pose proof (assembly_realizes_el x) as q ;
       revert q ;
       use factor_through_squash_hProp ;
       intros ( a₁ & Ha₁ ) ;
       pose proof (assembly_realizes_el y) as q ;
       revert q ;
       use factor_through_squash_hProp ;
       intros ( a₂ & Ha₂ ) ;
       use hinhpr ;
       refine (pair · a₁ · a₂ ,, _ ,, _)%ca ;
       [ rewrite combinatory_algebra_pr1_pair ; exact Ha₁
       | rewrite combinatory_algebra_pr2_pair ; exact Ha₂ ]).
Defined.

Proposition pullback_assembly_eq
            {A : combinatory_algebra}
            {X₁ X₂ X₃ : assembly A}
            {f : assembly_morphism X₁ X₃}
            {g : assembly_morphism X₂ X₃}
            {x₁ x₂ : pullback_assembly f g}
            (p : pr1 x₁ = pr1 x₂)
            (q : pr12 x₁ = pr12 x₂)
  : x₁ = x₂.
Proof.
  induction x₁ as [ x₁ [ y₁ H₁ ]].
  induction x₂ as [ x₂ [ y₂ H₂ ]].
  simpl in *.
  induction p, q.
  do 2 apply maponpaths.
  apply setproperty.
Qed.

Definition pullback_assembly_pr1
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism X₁ X₃)
           (g : assembly_morphism X₂ X₃)
  : assembly_morphism (pullback_assembly f g) X₁.
Proof.
  use make_assembly_morphism.
  - exact (λ z, pr1 z).
  - abstract
      (use hinhpr ;
       refine (π₁ ,, _) ;
       intros b w p ;
       exact (pr1 p)).
Defined.

Definition pullback_assembly_pr2
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism X₁ X₃)
           (g : assembly_morphism X₂ X₃)
  : assembly_morphism (pullback_assembly f g) X₂.
Proof.
  use make_assembly_morphism.
  - exact (λ z, pr12 z).
  - abstract
      (use hinhpr ;
       refine (π₂ ,, _) ;
       intros b w p ;
       exact (pr2 p)).
Defined.

Proposition pullback_assembly_comm
            {A : combinatory_algebra}
            {X₁ X₂ X₃ : assembly A}
            (f : assembly_morphism X₁ X₃)
            (g : assembly_morphism X₂ X₃)
  : comp_assembly_morphism (pullback_assembly_pr1 f g) f
    =
    comp_assembly_morphism (pullback_assembly_pr2 f g) g.
Proof.
  use assembly_morphism_eq.
  intro ; cbn.
  exact (pr22 x).
Qed.

Proposition pullback_assembly_map
            {A : combinatory_algebra}
            {X₁ X₂ X₃ X₄ : assembly A}
            (f : assembly_morphism X₁ X₃)
            (g : assembly_morphism X₂ X₃)
            (h : assembly_morphism X₄ X₁)
            (k : assembly_morphism X₄ X₂)
            (p : comp_assembly_morphism h f
                 =
                 comp_assembly_morphism k g)
  : assembly_morphism X₄ (pullback_assembly f g).
Proof.
  use make_assembly_morphism.
  - exact (λ x, h x ,, k x ,, assembly_morphism_eq_point p x).
  - abstract
      (pose proof (assembly_morphism_tracked h) as q ;
       revert q ;
       use factor_through_squash_hProp ;
       intros [ a₁ Ha₁ ] ;
       pose proof (assembly_morphism_tracked k) as q ;
       revert q ;
       use factor_through_squash_hProp ;
       intros [ a₂ Ha₂ ] ;
       use hinhpr ;
       refine (pairf · a₁ · a₂ ,, _)%ca ;
       intros b w q ; simpl ;
       rewrite combinatory_algebra_pr1_pair_fun ;
       rewrite combinatory_algebra_pr2_pair_fun ;
       specialize (Ha₁ b _ q) ;
       specialize (Ha₂ b _ q) ;
       exact (Ha₁ ,, Ha₂)).
Defined.

  
Definition pullbacks_cat_of_assembly
           (A : combinatory_algebra)
  : Pullbacks (cat_of_assembly A).
Proof.
  intros X₃ X₁ X₂ f g.
  use make_Pullback.
  - exact (pullback_assembly f g).
  - exact (pullback_assembly_pr1 f g).
  - exact (pullback_assembly_pr2 f g).
  - exact (pullback_assembly_comm f g).
  - intros X₄ h k p.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros h₁ h₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use assembly_morphism_eq ;
         intro x ;
         pose (assembly_morphism_eq_point (pr12 h₁ @ !(pr12 h₂)) x) as q₁ ;
         pose (assembly_morphism_eq_point (pr22 h₁ @ !(pr22 h₂)) x) as q₂ ;
         exact (pullback_assembly_eq q₁ q₂)).
    + refine (pullback_assembly_map f g h k p ,, _).
      abstract
        (split ;
         use assembly_morphism_eq ;
         intro ;
         apply idpath).
Defined.

(** * 6. Initial assembly *)
Definition initial_assembly
           (A : bi_algebra)
  : assembly A.
Proof.
  use make_assembly.
  - exact emptyset.
  - exact (λ _ _, hfalse).
  - abstract
      (intros ;
       apply propproperty).
  - intros x.
    induction x.
Defined.

Definition initial_assembly_morphism
           {A : bi_algebra}
           (X : assembly A)
  : assembly_morphism (initial_assembly A) X.
Proof.
  use make_assembly_morphism.
  - exact fromempty.
  - abstract
      (use hinhpr ;
       refine (I%bi ,, _) ;
       intros b w ;
       induction w).
Defined.

Definition initial_cat_of_assembly
           (A : bi_algebra)
  : Initial (cat_of_assembly A).
Proof.
  use make_Initial.
  - exact (initial_assembly A).
  - intros X.
    use make_iscontr.
    + exact (initial_assembly_morphism X).
    + abstract
        (intro f ;
         use assembly_morphism_eq ;
         intro x ;
         induction x).
Defined.

(** * 7. Binary coproducts of assemblies *)
Proposition sum_assembly_el
            {A : combinatory_algebra}
            (X₁ X₂ : assembly A)
            (z : setcoprod X₁ X₂)
  : (∃ (a : A),
     (π₁ · a = K
      ∧
      ∃ (x : X₁), π₂ · a ⊩ x ∧ z = inl x)%ca
     ∨
     (π₁ · a = K*
      ∧
      ∃ (y : X₂), π₂ · a ⊩ y ∧ z = inr y)%ca)%logic.
Proof.
  induction z as [ x | y ].
  - pose proof (assembly_realizes_el x) as p.
    revert p.
    use factor_through_squash_hProp.
    intros [ a Ha ].
    use hinhpr.
    refine (pair · K · a ,, _)%ca.
    use hdisj_in1.
    split.
    + rewrite combinatory_algebra_pr1_pair.
      apply idpath.
    + use hinhpr.
      refine (x ,, _ ,, idpath _).
      rewrite combinatory_algebra_pr2_pair.
      exact Ha.
  - pose proof (assembly_realizes_el y) as p.
    revert p.
    use factor_through_squash_hProp.
    intros [ a Ha ].
    use hinhpr.
    refine (pair · K* · a ,, _)%ca.
    use hdisj_in2.
    split.
    + rewrite combinatory_algebra_pr1_pair.
      apply idpath.
    + use hinhpr.
      refine (y ,, _ ,, idpath _).
      rewrite combinatory_algebra_pr2_pair.
      exact Ha.
Qed.

Definition sum_assembly
           {A : combinatory_algebra}
           (X₁ X₂ : assembly A)
  : assembly A.
Proof.
  use make_assembly.
  - exact (setcoprod X₁ X₂)%set.
  - exact (λ a z,
           (π₁ · a = K
            ∧
            ∃ (x : X₁), π₂ · a ⊩ x ∧ z = inl x)%ca
           ∨
           (π₁ · a = K*
            ∧
            ∃ (y : X₂), π₂ · a ⊩ y ∧ z = inr y)%ca)%logic.
  - abstract
      (intros ;
       apply propproperty).
  - exact (sum_assembly_el X₁ X₂).
Defined.

Definition inl_assembly_morphism
           {A : combinatory_algebra}
           (X₁ X₂ : assembly A)
  : assembly_morphism X₁ (sum_assembly X₁ X₂).
Proof.
  use make_assembly_morphism.
  - exact inl.
  - abstract
      (use hinhpr ;
       refine (pair · K ,, _)%ca ;
       intros a x p ;
       use hdisj_in1 ;
       rewrite combinatory_algebra_pr1_pair ;
       refine (idpath _ ,, _) ;
       use hinhpr ;
       refine (x ,, _ ,, idpath _) ;
       rewrite combinatory_algebra_pr2_pair ;
       exact p).
Defined.

Definition inr_assembly_morphism
           {A : combinatory_algebra}
           (X₁ X₂ : assembly A)
  : assembly_morphism X₂ (sum_assembly X₁ X₂).
Proof.
  use make_assembly_morphism.
  - exact inr.
  - abstract
      (use hinhpr ;
       refine (pair · K* ,, _)%ca ;
       intros a y p ;
       use hdisj_in2 ;
       rewrite combinatory_algebra_pr1_pair ;
       refine (idpath _ ,, _) ;
       use hinhpr ;
       refine (y ,, _ ,, idpath _) ;
       rewrite combinatory_algebra_pr2_pair ;
       exact p).
Defined.

Proposition sum_assembly_morphism_tracks
            {A : combinatory_algebra}
            {X₁ X₂ X₃ : assembly A}
            (f : assembly_morphism X₁ X₃)
            (g : assembly_morphism X₂ X₃)
  : ∃ (a : A),
    tracks_morphism (X₁ := sum_assembly X₁ X₂) (X₂ := X₃) a (sumofmaps f g).
Proof.
  pose proof (assembly_morphism_tracked f) as p.
  revert p.
  use factor_through_squash_hProp.
  intros [ a₁ Ha₁ ].
  pose proof (assembly_morphism_tracked g) as p.
  revert p.
  use factor_through_squash_hProp.
  intros [ a₂ Ha₂ ].
  use hinhpr.
  refine (sumf · a₁ · a₂ ,, _)%ca.
  intros b w p ; simpl.
  revert p.
  use factor_through_squash_hProp.
  intros pq.
  induction pq as [ [ p₁ p₂ ] | [ q₁ q₂ ] ].
  - revert p₂.
    use factor_through_squash_hProp.
    intros ( x & p₂ & p₃ ).
    rewrite p₃ ; simpl.
    specialize (Ha₁ (π₂ · b)%ca x p₂).
    rewrite (combinatory_algebra_sum_fun_inl _ _ _ p₁).
    exact Ha₁.
  - revert q₂.
    use factor_through_squash_hProp.
    intros ( y & q₂ & q₃ ).
    rewrite q₃ ; simpl.
    specialize (Ha₂ (π₂ · b)%ca y q₂).
    rewrite (combinatory_algebra_sum_fun_inr _ _ _ q₁).
    exact Ha₂.
Qed.

Definition sum_assembly_morphism
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism X₁ X₃)
           (g : assembly_morphism X₂ X₃)
  : assembly_morphism (sum_assembly X₁ X₂) X₃.
Proof.
  use make_assembly_morphism.
  - exact (sumofmaps f g).
  - exact (sum_assembly_morphism_tracks f g).
Defined.

Definition bincoproducts_cat_of_assembly
           (A : combinatory_algebra)
  : BinCoproducts (cat_of_assembly A).
Proof.
  intros X₁ X₂.
  use make_BinCoproduct.
  - exact (sum_assembly X₁ X₂).
  - exact (inl_assembly_morphism X₁ X₂).
  - exact (inr_assembly_morphism X₁ X₂).
  - intros X₃ f g.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros h₁ h₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use assembly_morphism_eq ;
         intro x ;
         induction x as [ x | y ] ;
         [ exact (assembly_morphism_eq_point (pr12 h₁ @ !(pr12 h₂)) x)
         | exact (assembly_morphism_eq_point (pr22 h₁ @ !(pr22 h₂)) y) ]).
    + refine (sum_assembly_morphism f g ,, _).
      abstract
        (split ;
         use assembly_morphism_eq ;
         intro x ;
         apply idpath).
Defined.

(** * 8. Natural numbers object of assemblies *)
Definition nat_assembly
           (A : combinatory_algebra)
  : assembly A.
Proof.
  use make_assembly.
  - exact natset.
  - exact (λ a n, a = ⌜ n ⌝).
  - abstract
      (intros ;
       apply setproperty).
  - abstract
      (intro n ;
       use hinhpr ;
       refine (⌜ n ⌝ ,, _) ;
       apply idpath).
Defined.

Definition nat_assembly_Z
           (A : combinatory_algebra)
  : assembly_morphism
      (terminal_assembly A)
      (nat_assembly A).
Proof.
  use make_assembly_morphism.
  - exact (λ _, 0).
  - abstract
      (use hinhpr ;
       refine (K · ⌜ 0 ⌝ ,, _)%ca ;
       intros a ? ? ; simpl ;
       rewrite combinatory_algebra_k_eq ;
       apply idpath).
Defined.

Definition nat_assembly_S
           (A : combinatory_algebra)
  : assembly_morphism
      (nat_assembly A)
      (nat_assembly A).
Proof.
  use make_assembly_morphism.
  - exact (λ n, 1 + n).
  - abstract
      (use hinhpr ;
       refine (succ ,, _) ;
       intros a ? p ; simpl ; simpl in p ;
       rewrite p ;
       rewrite combinatory_algebra_succ_eq ;
       apply idpath).
Defined.

Definition nat_assembly_rec_fn
           {A : combinatory_algebra}
           {X : assembly A}
           (zx : X)
           (sx : assembly_morphism X X)
  : nat_assembly A → X.
Proof.
  intro n.
  induction n as [ | n IHn ].
  - exact zx.
  - exact (sx IHn).
Defined.

Proposition nat_assembly_rec_tracks
            {A : combinatory_algebra}
            {X : assembly A}
            (zx : X)
            (sx : assembly_morphism X X)
  : ∃ (a : A), tracks_morphism a (nat_assembly_rec_fn zx sx).
Proof.
  pose proof (assembly_realizes_el zx) as p.
  revert p.
  use factor_through_squash_hProp.
  intros [ a_z Ha_z ].
  pose proof (assembly_morphism_tracked sx) as p.
  revert p.
  use factor_through_squash_hProp.
  intros [ a_s Ha_s ].
  use hinhpr.
  refine (combinatory_algebra_iter a_z a_s ,, _).
  intros b n p.
  simpl in p.
  rewrite p.
  clear p.
  induction n as [ | n IHn ].
  - rewrite combinatory_algebra_iter_Z.
    exact Ha_z.
  - rewrite combinatory_algebra_iter_succ.
    use (Ha_s _ (nat_assembly_rec_fn zx sx n)).
    apply IHn.
Qed.

Definition nat_assembly_rec
           {A : combinatory_algebra}
           {X : assembly A}
           (zx : X)
           (sx : assembly_morphism X X)
  : assembly_morphism
      (nat_assembly A)
      X.
Proof.
  use make_assembly_morphism.
  - exact (nat_assembly_rec_fn zx sx).
  - exact (nat_assembly_rec_tracks zx sx).
Defined.

Proposition nno_cat_of_assembly_unique
           {A : combinatory_algebra}
           (X : assembly A)
           (zx : assembly_morphism (terminal_assembly A) X)
           (sx : assembly_morphism X X)
  : isaprop
      (∑ (f : assembly_morphism (nat_assembly A) X),
       (comp_assembly_morphism (nat_assembly_Z A) f = zx)
       ×
       (comp_assembly_morphism (nat_assembly_S A) f
        =
        comp_assembly_morphism f sx)).
Proof.
  use invproofirrelevance.
  intros f₁ f₂.
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; apply isaset_assembly_morphism.
  }
  use assembly_morphism_eq.
  intro n.
  induction n as [ | n IHn ].
  - exact (assembly_morphism_eq_point (pr12 f₁ @ !(pr12 f₂)) tt).
  - refine (assembly_morphism_eq_point (pr22 f₁) _ @ _).
    refine (_ @ !(assembly_morphism_eq_point (pr22 f₂) _)).
    simpl.
    apply maponpaths.
    exact IHn.
Qed.

Definition nno_cat_of_assembly
           (A : combinatory_algebra)
  : NNO (terminal_cat_of_assembly A).
Proof.
  use make_NNO.
  - exact (nat_assembly A).
  - exact (nat_assembly_Z A).
  - exact (nat_assembly_S A).
  - refine (λ (X : assembly A)
              (zx : assembly_morphism (terminal_assembly A) X)
              (sx : assembly_morphism X X),
             _).
    use iscontraprop1.
    + exact (nno_cat_of_assembly_unique X zx sx).
    + abstract
        (refine (nat_assembly_rec (zx tt) sx ,, _) ;
         split ; use assembly_morphism_eq ;
         intro x ; [ | apply idpath ] ;
         induction x ;
         apply idpath).
Defined.

(** * 9. Exponentials *)
Definition function_assembly
           {A : combinatory_algebra}
           (X₁ X₂ : assembly A)
  : assembly A.
Proof.
  use make_assembly.
  - use make_hSet.
    + exact (assembly_morphism X₁ X₂).
    + apply isaset_assembly_morphism.
  - exact (λ (a : A) (f : assembly_morphism X₁ X₂), tracks_morphism a f).
  - abstract
      (intros ;
       apply propproperty).
  - abstract
      (intro f ;
       exact (assembly_morphism_tracked f)).
Defined.

Proposition eval_assembly_morphism_tracks
            {A : combinatory_algebra}
            (X₁ X₂ : assembly A)
  : ∃ a : A,
    tracks_morphism
      (X₁ := prod_assembly X₁ (function_assembly X₁ X₂))
      a
      (λ (xf : X₁ × assembly_morphism X₁ X₂), pr2 xf (pr1 xf)).
Proof.
  use hinhpr.
  refine (ε ,, _).
  intros a xf p.
  rewrite combinatory_algebra_eval_eq.
  induction xf as [ x f ].
  induction p as [ p₁ p₂ ].
  simpl in *.
  apply p₂.
  apply p₁.
Qed.

Definition eval_assembly_morphism
           {A : combinatory_algebra}
           (X₁ X₂ : assembly A)
  : assembly_morphism (prod_assembly X₁ (function_assembly X₁ X₂)) X₂.
Proof.
  use make_assembly_morphism.
  - exact (λ (xf : X₁ × assembly_morphism X₁ X₂), pr2 xf (pr1 xf)).
  - exact (eval_assembly_morphism_tracks X₁ X₂).
Defined.

Proposition lam_assembly_morphism_pt_tracks
            {A : combinatory_algebra}
            {X₁ X₂ X₃ : assembly A}
            (f : assembly_morphism (prod_assembly X₁ X₃) X₂)
            (x : X₃)
  : ∃ (a : A), tracks_morphism a (λ (y : X₁), f (y ,, x)).
Proof.
  pose proof (assembly_realizes_el x) as p.
  revert p.
  use factor_through_squash_hProp.
  intros ( a_x & Ha_x ).
  pose proof (assembly_morphism_tracked f) as p.
  revert p.
  use factor_through_squash_hProp.
  intros ( a_f & Ha_f ).
  use hinhpr.
  refine (lam · a_f · a_x ,, _)%ca.
  intros b y p.
  rewrite combinatory_algebra_lam_eq.
  use Ha_f.
  split.
  - rewrite combinatory_algebra_pr1_pair ; simpl.
    exact p.
  - rewrite combinatory_algebra_pr2_pair ; simpl.
    exact Ha_x.
Qed.

Definition lam_assembly_morphism_pt
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism (prod_assembly X₁ X₃) X₂)
           (x : X₃)
  : assembly_morphism X₁ X₂.
Proof.
  use make_assembly_morphism.
  - exact (λ y, f (y ,, x)).
  - exact (lam_assembly_morphism_pt_tracks f x).
Defined.

Proposition lam_assembly_morphism_tracks
            {A : combinatory_algebra}
            {X₁ X₂ X₃ : assembly A}
            (f : assembly_morphism (prod_assembly X₁ X₃) X₂)
  : ∃ (a : A),
    tracks_morphism
      a
      (X₁ := X₃)
      (X₂ := function_assembly X₁ X₂)
      (lam_assembly_morphism_pt f).
Proof.
  pose proof (assembly_morphism_tracked f) as p.
  revert p.
  use factor_through_squash_hProp.
  intros ( a_f & Ha_f ).
  use hinhpr.
  refine (lam · a_f ,, _)%ca.
  intros b x p a y q.
  rewrite combinatory_algebra_lam_eq.
  simpl.
  use Ha_f.
  split.
  - rewrite combinatory_algebra_pr1_pair ; simpl.
    exact q.
  - rewrite combinatory_algebra_pr2_pair ; simpl.
    exact p.
Qed.

Definition lam_assembly_morphism
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism (prod_assembly X₁ X₃) X₂)
  : assembly_morphism X₃ (function_assembly X₁ X₂).
Proof.
  use make_assembly_morphism.
  - exact (lam_assembly_morphism_pt f).
  - exact (lam_assembly_morphism_tracks f).
Defined.

Definition exponentials_cat_of_assembly
           (A : combinatory_algebra)
  : Exponentials (binproducts_cat_of_assembly A).
Proof.
  intros X₁.
  use coreflections_to_is_left_adjoint.
  intros X₂.
  use make_coreflection.
  - use make_coreflection_data.
    + exact (function_assembly X₁ X₂).
    + exact (eval_assembly_morphism X₁ X₂).
  - intro X₃.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros f₁ f₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use assembly_morphism_eq ;
         intro x ;
         use assembly_morphism_eq ;
         intro y ;
         exact (assembly_morphism_eq_point (!(pr2 f₁) @ pr2 f₂) (y ,, x))).
    + simple refine (_ ,, _).
      * exact (lam_assembly_morphism (coreflection_data_arrow X₃)).
      * abstract
          (use assembly_morphism_eq ;
           intro x ;
           apply idpath).
Defined.

(** * 10. Fibers *)
Definition assembly_fiber
           {A : combinatory_algebra}
           {X₁ X₂ : assembly A}
           (f : assembly_morphism X₁ X₂)
           (y : X₂)
  : assembly A.
Proof.
  use make_assembly.
  - exact (hfiber_hSet f y).
  - exact (λ a xp, a ⊩ pr1 xp).
  - abstract
      (intros ;
       apply propproperty).
  - abstract
      (intros xp ;
       exact (assembly_realizes_el (pr1 xp))).
Defined.
