(**

 Linear ∏-types

 We verify that the linear realizability model has linear ∏-types, which means that every
 substitution is a monoidal left adjoint. For this, it suffices to check that every
 substitution functor has a right adjoint, and we do not have to verify that the right adjoint,
 unit, and counit are monoidal themselves. This is because we already verified that the
 substitution functors are strong monoidal, and because an adjunction is monoidal iff the left
 adjoint is strong monoidal. The Beck-Chevalley condition for ∏-types follows from the
 Beck-Chevalley condition for ∑-types.

 Contents
 1. Linear ∏-types
 2. Evaluation and abstraction
 3. The adjunction

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Require Import SetFamilies.
Require Import PreservesMonoidalClosed.
Require Import FiberwiseMonoidal.
Require Import Basics.BIAlgebra.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Combinators.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Assemblies.LinearAssemblyMonoidal.
Require Import Types.LinearSigma.

Local Open Scope lca.
Local Open Scope assembly.
Local Open Scope cat.

Section LinearPi.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  Section PiType.
    Context {Γ₁ Γ₂ : assembly AC}
            (s : assembly_morphism Γ₁ Γ₂).

    (** * 1. Linear ∏-types *)
    Definition tracks_lin_dependent_mor
               {X : dep_assembly Γ₁}
               (a : A)
               {y : Γ₂}
               (f : dep_prod_set_fam s X y)
      : hProp
      := (∀ (x : assembly_fiber (A := AC) s y) (b : A), b ⊩ x ⇒ (a · !b)%lca ⊩ f x)%logic.

    Definition lin_dependent_mor
               (X : dep_assembly Γ₁)
               (x : Γ₂)
      : UU
      := ∑ (f : dep_prod_set_fam s X x), ∃ a, tracks_lin_dependent_mor a f.

    Definition make_lin_dependent_mor
               {X : dep_assembly Γ₁}
               {x : Γ₂}
               (f : dep_prod_set_fam s X x)
               (p : ∃ a, tracks_lin_dependent_mor a f)
      : lin_dependent_mor X x
      := f ,, p.
    
    Coercion lin_dependent_mor_to_dep_prod_set_fam
             {X : dep_assembly Γ₁}
             {x : Γ₂}
             (f : lin_dependent_mor X x)
      : dep_prod_set_fam s X x
      := pr1 f.
    
    Definition lin_dependent_mor_to_mor
               {X : dep_assembly Γ₁}
               {x : Γ₂}
               (f : lin_dependent_mor X x)
               (y : Γ₁)
               (p : s y = x)
      : X y
      := pr1 f (y ,, p).

    Coercion lin_dependent_mor_to_mor : lin_dependent_mor >-> Funclass.

    Proposition lin_dependent_mor_tracker
                {X : dep_assembly Γ₁}
                {x : Γ₂}
                (f : lin_dependent_mor X x)
      : ∃ a, tracks_lin_dependent_mor a f.
    Proof.
      exact (pr2 f).
    Qed.

    Proposition lin_dependent_mor_eq
                {X : dep_assembly Γ₁}
                {x : Γ₂}
                {f g : lin_dependent_mor X x}
                (p : ∏ (y : Γ₁)
                       (q : s y = x),
                     f y q = g y q)
      : f = g.
    Proof.
      use subtypePath.
      {
        intro.
        apply propproperty.
      }
      use funextsec.
      intros y.
      apply p.
    Qed.
    
    Proposition isaset_lin_dependent_mor
                (X : dep_assembly Γ₁)
                (x : Γ₂)
      : isaset (lin_dependent_mor X x).
    Proof.
      use isaset_total2.
      - apply setproperty.
      - intro.
        apply isasetaprop.
        apply propproperty.
    Qed.
    
    Definition linear_pi_dep_assembly
               (X : dep_assembly Γ₁)
      : dep_assembly Γ₂.
    Proof.
      intro x.
      use make_assembly.
      - use make_hSet.
        + exact (lin_dependent_mor X x).
        + exact (isaset_lin_dependent_mor X x).
      - exact (λ a f, tracks_lin_dependent_mor a (pr1 f)).
      - abstract
          (intros ;
           apply propproperty).
      - exact lin_dependent_mor_tracker.
    Defined.

    (** * 2. Evaluation and abstraction *)
    Definition linear_pi_dep_assembly_eval
               (X : dep_assembly Γ₁)
      : lin_dep_assembly_morphism
          (lin_dep_assembly_subst s (linear_pi_dep_assembly X))
          X
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ (x : Γ₁) (f : lin_dependent_mor X (s x)), f x (idpath _)).
      - abstract
          (use hinhpr ;
           refine (C · I ,, _)%lca ;
           intros x f a₁ a₂ p q ;
           specialize (q (x ,, idpath _) a₁ p) ;
           rewrite linear_combinatory_algebra_c_eq ;
           rewrite linear_combinatory_algebra_i_eq ;
           exact q).
    Defined.

    Definition linear_pi_dep_assembly_lam_pt
               {X : dep_assembly Γ₁}
               {X' : dep_assembly Γ₂}
               (g : lin_dep_assembly_morphism
                      (lin_dep_assembly_subst s X')
                      X
                      (id_assembly_morphism _))
               {x : Γ₂}
               (xx : X' x)
      : lin_dependent_mor X x.
    Proof.
      use make_lin_dependent_mor.
      - exact (λ y, g _ (transportb X' (pr2 y) xx)).
      - abstract
          (pose proof (lin_dep_assembly_morphism_function_track g) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a & p) ;
           pose proof (assembly_realizes_el xx) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros (b & q) ;
           use hinhpr ;
           refine (C · a · b ,, _)%lca ;
           intros y c r ;
           rewrite linear_combinatory_algebra_c_eq ;
           use (p (pr1 y) (transportb X' (pr2 y) xx) c b r) ;
           use (dep_assembly_transportf_realizes (A := AC)) ;
           exact q).
    Defined.

    Proposition linear_pi_dep_assembly_lam_pt_tracker
                {X : dep_assembly Γ₁}
                {X' : dep_assembly Γ₂}
                (g : lin_dep_assembly_morphism
                       (lin_dep_assembly_subst s X')
                       X
                       (id_assembly_morphism _))
      : lin_dep_assembly_morphism_tracker
          (X₁ := X')
          (X₂ := linear_pi_dep_assembly X)
          (s := id_assembly_morphism _)
          (λ x y, linear_pi_dep_assembly_lam_pt g y).
    Proof.
      pose proof (lin_dep_assembly_morphism_function_track g) as p.
      revert p.
      use factor_through_squash_hProp.
      intros (a & p).
      use hinhpr.
      refine (lca_lin_lam · a ,, _)%lca.
      intros x xx b₁ b₂ q₁ q₂ (y & r) c r' ; simpl in r, r' ; simpl.
      induction r ; cbn.
      rewrite lca_lin_lam_eq.
      apply p.
      - exact r'.
      - exact q₂.
    Qed.
    
    Definition linear_pi_dep_assembly_lam
               {X : dep_assembly Γ₁}
               {X' : dep_assembly Γ₂}
               (g : lin_dep_assembly_morphism
                      (lin_dep_assembly_subst s X')
                      X
                      (id_assembly_morphism _))
      : lin_dep_assembly_morphism X' (linear_pi_dep_assembly X) (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x y, linear_pi_dep_assembly_lam_pt g y).
      - exact (linear_pi_dep_assembly_lam_pt_tracker g).
    Defined.

    (** * 3. The adjunction *)
    Definition pi_coreflection_lin_dep_assembly_data
               (X : dep_assembly Γ₁)
      : coreflection_data
          (X : fiber_category (disp_cat_of_lin_dep_assembly A) _)
          (fiber_functor_from_cleaving
             (disp_cat_of_lin_dep_assembly A)
             (lin_dep_assembly_cleaving A)
             s).
    Proof.
      use make_coreflection_data.
      - exact (linear_pi_dep_assembly X).
      - exact (linear_pi_dep_assembly_eval X).
    Defined.

    Definition pi_coreflection_lin_dep_assembly_laws
               (X : dep_assembly Γ₁)
      : is_coreflection (pi_coreflection_lin_dep_assembly_data X).
    Proof.
      intros [ X' g ] ; simpl in X', g.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ;
           [ intro ; apply homset_property | ] ;
           use lin_dep_assembly_morphism_eq ;
           intros x xx ; simpl in xx ;
           use lin_dependent_mor_eq ;
           intros y q ; cbn in q ;
           induction q ;
           pose (p := lin_dep_assembly_morphism_eq_point (pathsinv0 (pr2 φ₁) @ pr2 φ₂) xx) ;
           refine (pathsinv0 _ @ p @ _) ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           (etrans ;
            [ apply maponpaths ;
              apply fiber_functor_from_cleaving_lin_dep_assembly
            | ]) ;
           apply idpath).
      - simple refine (_ ,, _).
        + exact (linear_pi_dep_assembly_lam g).
        + abstract
            (use lin_dep_assembly_morphism_eq ;
             intros x y ; simpl in y ;
             apply pathsinv0 ;
             refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
             etrans ;
             [ apply maponpaths ;
               apply fiber_functor_from_cleaving_lin_dep_assembly
             | ] ;
             cbn ;
             apply idpath).
    Defined.
    
    Definition dependent_product_lin_dep_assembly
      : dependent_product (lin_dep_assembly_cleaving A) s.
    Proof.
      use coreflections_to_is_left_adjoint.
      intros X.
      use make_coreflection.
      - exact (pi_coreflection_lin_dep_assembly_data X).
      - exact (pi_coreflection_lin_dep_assembly_laws X).
    Defined.
  End PiType.

  Definition lin_dep_assembly_dependent_products
    : has_dependent_products (lin_dep_assembly_cleaving A).
  Proof.
    simple refine (_ ,, _).
    - intros Γ₁ Γ₂ s.
      exact (dependent_product_lin_dep_assembly s).
    - intros Γ₁ Γ₂ Γ₃ Γ₄ s₁ s₂ s₃ s₄ p Hp.
      use right_from_left_beck_chevalley.
      + apply lin_dep_assembly_dependent_sums.
      + apply lin_dep_assembly_dependent_sums.
      + apply lin_dep_assembly_dependent_sums.
        use is_symmetric_isPullback.
        exact Hp.
  Defined.
End LinearPi.
