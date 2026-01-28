(**

 Dependent products of assemblies

 In this file, we show that the comprehension category of assemblies supports all
 dependent products. Specifically, we show that each substitution functor has a
 right adjoint. Note that the Beck-Chevalley condition for dependent products
 follows from the Beck-Chevalley condition for dependent sums.

 Contents
 1. Dependent morphisms
 2. Dependent products of assemblies

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DualBeckChevalley.

Require Import BeckChevalleyChosen.
Require Import SetFamilies.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Types.DependentSums.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

Section DependentAssemblyProduct.
  Context {A : combinatory_algebra}.

  Section DepProd.
    Context {Γ₁ Γ₂ : assembly A}
            (s : assembly_morphism Γ₁ Γ₂)
            (X : dep_assembly Γ₁).

    (** * 1. Dependent morphisms *)
    Definition tracks_dependent_mor
               (a : A)
               {y : Γ₂}
               (f : dep_prod_set_fam s X y)
      : hProp
      := (∀ (x : assembly_fiber s y) (b : A), b ⊩ x ⇒ (a · b)%ca ⊩ f x)%logic.

    Definition dependent_mor_assembly
               (y : Γ₂)
      : UU
      := ∑ (f : dep_prod_set_fam s X y), ∃ (a : A), tracks_dependent_mor a f.

    Definition make_dependent_mor_assembly
               {y : Γ₂}
               (f : dep_prod_set_fam s X y)
               (H : ∃ (a : A), tracks_dependent_mor a f)
      : dependent_mor_assembly y
      := f ,, H.
    
    Proposition isaset_dependent_mor_assembly
                (y : Γ₂)
      : isaset (dependent_mor_assembly y).
    Proof.
      use isaset_total2.
      - apply setproperty.
      - intro.
        apply isasetaprop.
        apply propproperty.
    Qed.
                
    Coercion dependent_mor_assembly_to_mor
             {y : Γ₂}
             (f : dependent_mor_assembly y)
      : dep_prod_set_fam s X y
      := pr1 f.

    Definition dependent_mor_assembly_tracker
               {y : Γ₂}
               (f : dependent_mor_assembly y)
      : ∃ (a : A), tracks_dependent_mor a f
      := pr2 f.

    Proposition dependent_mor_assembly_eq
                {y : Γ₂}
                {f₁ f₂ : dependent_mor_assembly y}
                (p : ∏ (x : hfiber_hSet s y), pr1 f₁ x = pr1 f₂ x)
      : f₁ = f₂.
    Proof.
      use subtypePath.
      {
        intro.
        apply propproperty.
      }
      use dep_prod_set_fam_eq.
      exact p.
    Qed.

    (** * 2. Dependent products of assemblies *)
    Definition dep_assembly_dep_prod
      : dep_assembly Γ₂.
    Proof.
      refine (λ y, _).
      use make_assembly.
      - use make_hSet.
        + exact (dependent_mor_assembly y).
        + apply isaset_dependent_mor_assembly.
      - exact (λ (a : A) (f : dependent_mor_assembly y), tracks_dependent_mor a f).
      - abstract
          (intros ;
           apply propproperty).
      - abstract
          (intros f ;
           exact (dependent_mor_assembly_tracker f)).
    Defined.

    Definition dep_assembly_dep_prod_eval
      : dep_assembly_morphism
          (dep_assembly_subst s dep_assembly_dep_prod)
          X
          (id_assembly_morphism Γ₁).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ (x : Γ₁) (f : dependent_mor_assembly (s x)),
               dep_prod_set_fam_eval x f).
      - abstract
          (use hinhpr ;
           refine (T ,, _) ;
           intros x ff b₁ b₂ p₁ p₂ ;
           rewrite combinatory_algebra_t_eq ;
           use p₂ ;
           exact p₁).
    Defined.

    Definition dep_assembly_dependent_products_coreflection_data
      : coreflection_data
          (D := (disp_cat_of_dep_assembly A)[{Γ₁}])
          X
          (fiber_functor_from_cleaving
             (disp_cat_of_dep_assembly A)
             (dep_assembly_cleaving A)
             s).
    Proof.
      use make_coreflection_data.
      - exact dep_assembly_dep_prod.
      - exact dep_assembly_dep_prod_eval.
    Defined.

    Section UMP.
      Context {X' : dep_assembly Γ₂}
              (f : dep_assembly_morphism
                     (dep_assembly_subst s X')
                     X
                     (id_assembly_morphism Γ₁)).

      Definition dep_assembly_dep_prod_lam
        : dep_assembly_morphism
            X'
            dep_assembly_dep_prod
            (id_assembly_morphism Γ₂).
      Proof.
        use make_dep_assembly_morphism.
        - intros y yy.
          use make_dependent_mor_assembly.
          + exact (dep_prod_set_fam_lam X' f yy).
          + abstract
              (pose proof (dep_assembly_morphism_function_track f) as q ;
               revert q ;
               use factor_through_squash_hProp ;
               intros ( a & p ) ;
               pose proof (assembly_realizes_el yy) as q ;
               revert q ;
               use factor_through_squash_hProp ;
               intros ( a' & p' ) ;
               use hinhpr ;
               refine (C · a · a' ,, _)%ca ;
               intros x b q ; cbn ;
               rewrite combinatory_algebra_c_eq ;
               use (p _ _ _ _ q) ;
               use dep_assembly_transportf_realizes ;
               exact p').
        - abstract
            (pose proof (dep_assembly_morphism_function_track f) as q ;
             revert q ;
             use factor_through_squash_hProp ;
             intros ( a & p ) ;
             use hinhpr ;
             refine (lam_d · a ,, _)%ca ;
             intros y yy b₁ b₂ q₁ q₂ x b₃ q₃ ;
             rewrite combinatory_algebra_dep_lam_eq ;
             use (p (pr1 x) _ _ _ q₃) ;
             use dep_assembly_transportf_realizes ;
             exact q₂).
      Defined.

      Proposition dep_assembly_dep_prod_beta
        : f
          =
          #(fiber_functor_from_cleaving
              (disp_cat_of_dep_assembly A)
              (dep_assembly_cleaving A)
              s)
            dep_assembly_dep_prod_lam
          · dep_assembly_dep_prod_eval.
      Proof.
        use dep_assembly_morphism_eq.
        intros x xx.
        refine (!_).
        etrans.
        {
          apply fiber_comp_dep_assembly.
        }
        etrans.
        {
          apply maponpaths.
          use fiber_functor_from_cleaving_dep_assembly.
        }
        apply idpath.
      Qed.

      Proposition dep_assembly_dep_prod_eta
        : isaprop
            (∑ g,
             f
             =
             #(fiber_functor_from_cleaving
                 (disp_cat_of_dep_assembly A)
                 (dep_assembly_cleaving A)
                 s)
               g
             · dep_assembly_dep_prod_eval).
      Proof.
        use invproofirrelevance.
        intros g₁ g₂.
        use subtypePath.
        {
          intro.
          apply isaset_dep_assembly_morphism.
        }
        use dep_assembly_morphism_eq.
        intros y yy.
        use dependent_mor_assembly_eq.
        intros ( x & p ).
        cbn in p.
        induction p.
        pose (p := dep_assembly_morphism_eq_point
                     (!(pr2 g₁) @ pr2 g₂)
                     yy).
        refine (_ @ p @ _).
        - refine (!_).
          etrans.
          {
            apply fiber_comp_dep_assembly.
          }
          etrans.
          {
            apply maponpaths.
            use fiber_functor_from_cleaving_dep_assembly.
          }
          cbn.
          apply idpath.
        - etrans.
          {
            apply fiber_comp_dep_assembly.
          }
          etrans.
          {
            apply maponpaths.
            use fiber_functor_from_cleaving_dep_assembly.
          }
          cbn.
          apply idpath.
      Qed.          
    End UMP.

    Proposition dep_assembly_dependent_products_coreflection_laws
      : is_coreflection dep_assembly_dependent_products_coreflection_data.
    Proof.
      intros X'.
      pose (f := coreflection_data_arrow X').
      use iscontraprop1.
      - exact (dep_assembly_dep_prod_eta f).
      - simple refine (_ ,, _).
        + exact (dep_assembly_dep_prod_lam f).
        + exact (dep_assembly_dep_prod_beta f).
    Defined.
  End DepProd.

  Definition dep_assembly_dependent_products_type
             {Γ₁ Γ₂ : assembly A}
             (s : assembly_morphism Γ₁ Γ₂)
    : dependent_product (dep_assembly_cleaving A) s.
  Proof.
    use coreflections_to_is_left_adjoint.
    intro X.
    use make_coreflection.
    - exact (dep_assembly_dependent_products_coreflection_data s X).
    - exact (dep_assembly_dependent_products_coreflection_laws s X).
  Defined.
  
  Definition dep_assembly_dependent_products
    : has_dependent_products (dep_assembly_cleaving A).
  Proof.
    simple refine (_ ,, _).
    - intros Γ₁ Γ₂ s.
      exact (dep_assembly_dependent_products_type s).
    - intros Γ₁ Γ₂ Γ₃ Γ₄ s₁ s₂ s₃ s₄ p Hp.
      use right_from_left_beck_chevalley.
      + apply dep_assembly_dependent_sums.
      + apply dep_assembly_dependent_sums.
      + apply dep_assembly_dependent_sums.
        use is_symmetric_isPullback.
        exact Hp.
  Defined.
End DependentAssemblyProduct.
