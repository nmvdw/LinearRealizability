(**

 Fiberwise structure for the category of assemblies

 We show that the displayed category of assemblies has fiberwise initial objects, (binary)
 coproducts, and (binary) products. To do so, we use the expected constructions for assemblies.
 The fact that the substitution functors preserve these limits and colimits follows from the
 fact that substitution has a left- and a right adjoint.

 Contents
 1. Fiberwise initial object
 2. Fiberwise binary products
 3. Cartesian monoidal structure
 4. Binary coproducts

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.

Require Import Basics.BIAlgebra.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Combinators.
Require Import Basics.Completeness.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Types.DependentSums.
Require Import Types.DependentProducts.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

Section FiberStructure.
  Context {A : combinatory_algebra}.

  Section FixFiber.
    Context (Γ : assembly A).

    Let Fib : category := (disp_cat_of_dep_assembly A) [{Γ}].

    (** * 1. Fiberwise initial object *)
    Definition initial_obj_dep_assembly
      : dep_assembly Γ
      := λ x, initial_assembly A.

    Definition initial_dep_assembly_mor
               (X : dep_assembly Γ)
      : dep_assembly_morphism
          initial_obj_dep_assembly
          X
          (id_assembly_morphism _).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x, fromempty).
      - abstract
          (use hinhpr ;
           refine (I ,, _) ;
           intros x xx ;
           induction xx).
    Defined.

    Definition initial_dep_assembly
      : Initial Fib.
    Proof.
      use make_Initial.
      - exact initial_obj_dep_assembly.
      - intro X.
        use make_iscontr.
        + exact (initial_dep_assembly_mor X).
        + abstract
            (intro f ;
             use dep_assembly_morphism_eq ;
             intros x xx ;
             induction xx).
    Defined.

    (** * 2. Fiberwise binary products *)
    Definition binprod_dep_assembly
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly Γ
      := λ x, prod_assembly (X₁ x) (X₂ x).

    Definition binprod_dep_assembly_pr1
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly_morphism
          (binprod_dep_assembly X₁ X₂)
          X₁
          (id_assembly_morphism _).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x xy, pr1 xy).
      - abstract
          (use hinhpr ;
           refine ((Λ (Co π₁ • V 1)) ,, _)%ca ;
           intros x (y₁ & y₂) a₁ a₂ p q ;
           simpl in * ;
           refine (transportb (λ z, z ⊩ _) _ (pr1 q)) ;
           etrans ;
           [ apply maponpaths_2 ;
             apply lam_term_multiple
           | ] ;
           rewrite lam_term_single ;
           simpl ;
           apply idpath).
    Defined.

    Definition binprod_dep_assembly_pr2
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly_morphism
          (binprod_dep_assembly X₁ X₂)
          X₂
          (id_assembly_morphism _).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x xy, pr2 xy).
      - abstract
          (use hinhpr ;
           refine ((Λ (Co π₂ • V 1)) ,, _)%ca ;
           intros x (y₁ & y₂) a₁ a₂ p q ;
           simpl in * ;
           refine (transportb (λ z, z ⊩ _) _ (pr2 q)) ;
           etrans ;
           [ apply maponpaths_2 ;
             apply lam_term_multiple
           | ] ;
           rewrite lam_term_single ;
           simpl ;
           apply idpath).
    Defined.

    Definition binprod_dep_assembly_pair
               {Z X₁ X₂ : dep_assembly Γ}
               (f : dep_assembly_morphism Z X₁ (id_assembly_morphism _))
               (g : dep_assembly_morphism Z X₂ (id_assembly_morphism _))
      : dep_assembly_morphism
          Z
          (binprod_dep_assembly X₁ X₂)
          (id_assembly_morphism _).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x z, f x z ,, g x z).
      - abstract
          (pose proof (dep_assembly_morphism_function_track f) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a₁ & p₁) ;
           pose proof (dep_assembly_morphism_function_track g) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a₂ & p₂) ;
           use hinhpr ;
           cbn ;
           refine ((Λ (Co pair • (Co a₁ • V 0 • V 1) • (Co a₂ • V 0 • V 1))) ,, _) ;
           intros x z b₁ b₂ q₁ q₂ ;
           specialize (p₁ x z b₁ b₂ q₁ q₂) ;
           specialize (p₂ x z b₁ b₂ q₁ q₂) ;
           split ;
           [ refine (transportb (λ z, z ⊩ _) _ p₁)
           | refine (transportb (λ z, z ⊩ _) _ p₂) ] ;
           (etrans ;
            [ apply maponpaths ;
              apply maponpaths_2 ;
              apply lam_term_multiple
            | ]) ;
           rewrite lam_term_single ;
           simpl ;
           [ rewrite combinatory_algebra_pr1_pair
           | rewrite combinatory_algebra_pr2_pair ] ;
           apply idpath).
    Defined.

    Definition binproducts_dep_assembly
      : BinProducts Fib.
    Proof.
      intros X₁ X₂.
      use make_BinProduct.
      - exact (binprod_dep_assembly X₁ X₂).
      - exact (binprod_dep_assembly_pr1 X₁ X₂).
      - exact (binprod_dep_assembly_pr2 X₁ X₂).
      - intros Z f g.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros h₁ h₂ ;
             use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             use dep_assembly_morphism_eq ;
             intros x xx ;
             pose (dep_assembly_morphism_eq_point (pr12 h₁ @ pathsinv0 (pr12 h₂)) xx)
               as q₁ ;
             pose (dep_assembly_morphism_eq_point (pr22 h₁ @ pathsinv0 (pr22 h₂)) xx)
               as q₂ ;
             pose (pathsinv0 (fiber_comp_dep_assembly _ _ _)
                   @ q₁
                   @ fiber_comp_dep_assembly _ _ _) as q₁' ;
             pose (pathsinv0 (fiber_comp_dep_assembly _ _ _)
                   @ q₂
                   @ fiber_comp_dep_assembly _ _ _) as q₂' ;
             exact (pathsdirprod q₁' q₂')).
        + simple refine (_ ,, _ ,, _). 
          * exact (binprod_dep_assembly_pair f g).
          * abstract
              (use dep_assembly_morphism_eq ;
               intros x xx ;
               apply fiber_comp_dep_assembly).
          * abstract
              (use dep_assembly_morphism_eq ;
               intros x xx ;
               apply fiber_comp_dep_assembly).
    Defined.

    (** * 3. Cartesian monoidal structure *)
    Definition dependent_assembly_cartesian_monoidalcat
      : monoidal_cat
      := cartesian_monoidalcat
           _
           binproducts_dep_assembly
           (fiberwise_terminal_object_dep_assembly Γ).

    Definition dependent_assembly_cartesian_monoidalcat_symmetric
      : symmetric dependent_assembly_cartesian_monoidalcat
      := symmetric_cartesian_monoidalcat _ _ _.

    Definition dependent_assembly_cartesian_symmetric_mon_cat
      : sym_monoidal_cat
      := dependent_assembly_cartesian_monoidalcat
         ,,
         dependent_assembly_cartesian_monoidalcat_symmetric.

    (** * 4. Binary coproducts *)
    Definition bincoprod_dep_assembly
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly Γ
      := λ x, sum_assembly (X₁ x) (X₂ x).

    Definition bincoprod_dep_assembly_inl
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly_morphism
          X₁
          (bincoprod_dep_assembly X₁ X₂)
          (id_assembly_morphism _).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x xy, inl xy).
      - abstract
          (use hinhpr ;
           refine ((Λ (Co (pair · K) • V 1)) ,, _)%ca ;
           intros x xx b₁ b₂ p₁ p₂ ;
           assert ((Λ Co (pair · K) • V 1) · b₁ · b₂ = pair · K · b₂)%ca as -> ;
           [  etrans ;
              [ apply maponpaths_2 ;
                apply lam_term_multiple
              | ] ;
              rewrite lam_term_single ;
              simpl ;
              apply idpath
           | ] ;
           use hinhpr ;
           use inl ;
           rewrite combinatory_algebra_pr1_pair ;
           rewrite combinatory_algebra_pr2_pair ;
           refine (idpath _ ,, _) ;
           use hinhpr ;
           refine (xx ,, _ ,, idpath _) ;
           exact p₂).
    Defined.

    Definition bincoprod_dep_assembly_inr
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly_morphism
          X₂
          (bincoprod_dep_assembly X₁ X₂)
          (id_assembly_morphism _).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x xy, inr xy).
      - abstract
          (use hinhpr ;
           refine ((Λ (Co (pair · K*) • V 1)) ,, _)%ca ;
           intros x xx b₁ b₂ p₁ p₂ ;
           assert ((Λ Co (pair · K*) • V 1) · b₁ · b₂ = pair · K* · b₂)%ca as -> ;
           [  etrans ;
              [ apply maponpaths_2 ;
                apply lam_term_multiple
              | ] ;
              rewrite lam_term_single ;
              simpl ;
              apply idpath
           | ] ;
           use hinhpr ;
           use inr ;
           rewrite combinatory_algebra_pr1_pair ;
           rewrite combinatory_algebra_pr2_pair ;
           refine (idpath _ ,, _) ;
           use hinhpr ;
           refine (xx ,, _ ,, idpath _) ;
           exact p₂).
    Defined.

    Definition bincoprod_dep_assembly_copair_map
               {X₁ X₂ Z : dep_assembly Γ}
               (f : dep_assembly_morphism X₁ Z (id_assembly_morphism _))
               (g : dep_assembly_morphism X₂ Z (id_assembly_morphism _))
               (x : Γ)
               (xy : bincoprod_dep_assembly X₁ X₂ x)
      : Z x.
    Proof.
      induction xy as [ y | y ].
      - exact (f x y).
      - exact (g x y).
    Defined.

    Proposition bincoprod_dep_assembly_copair_tracker
                {X₁ X₂ Z : dep_assembly Γ}
                (f : dep_assembly_morphism X₁ Z (id_assembly_morphism _))
                (g : dep_assembly_morphism X₂ Z (id_assembly_morphism _))
      : dep_assembly_morphism_tracker
          (s := id_assembly_morphism _)
          (bincoprod_dep_assembly_copair_map f g).
    Proof.
      pose proof (dep_assembly_morphism_function_track f) as p.
      revert p.
      use factor_through_squash_hProp.
      intros (a₁ & p₁).
      pose proof (dep_assembly_morphism_function_track g) as p.
      revert p.
      use factor_through_squash_hProp.
      intros (a₂ & p₂).
      use hinhpr.
      refine (sumf_fib · a₁ · a₂ ,, _)%ca.
      intros x xx b₁ b₂ q₁.
      use factor_through_squash_hProp.
      intros [ [ q₂ q₃ ] | [ q₂ q₃ ] ].
      - revert q₃.
        use factor_through_squash_hProp.
        intros (z & r₁ & r₂).
        specialize (p₁ x z b₁ (π₂ · b₂)%ca q₁ r₁).
        simpl.
        rewrite combinatory_algebra_sum_fun_fib_inl ; try assumption.
        induction xx as [ y | y ].
        + apply ii1_injectivity in r₂.
          rewrite r₂.
          apply p₁.
        + apply fromempty.
          exact (negpathsii2ii1 _ _ r₂).
      - revert q₃.
        use factor_through_squash_hProp.
        intros (z & r₁ & r₂).
        specialize (p₂ x z b₁ (π₂ · b₂)%ca q₁ r₁).
        simpl.
        rewrite combinatory_algebra_sum_fun_fib_inr ; try assumption.
        induction xx as [ y | y ].
        + apply fromempty.
          exact (negpathsii1ii2 _ _ r₂).
        + apply ii2_injectivity in r₂.
          rewrite r₂.
          apply p₂.
    Qed.
    
    Definition bincoprod_dep_assembly_copair
               {X₁ X₂ Z : dep_assembly Γ}
               (f : dep_assembly_morphism X₁ Z (id_assembly_morphism _))
               (g : dep_assembly_morphism X₂ Z (id_assembly_morphism _))
      : dep_assembly_morphism
          (bincoprod_dep_assembly X₁ X₂)
          Z
          (id_assembly_morphism _).
    Proof.
      use make_dep_assembly_morphism.
      - exact (bincoprod_dep_assembly_copair_map f g).
      - exact (bincoprod_dep_assembly_copair_tracker f g).
    Defined.

    Definition bincoproducts_dep_assembly
      : BinCoproducts Fib.
    Proof.
      intros X₁ X₂.
      use make_BinCoproduct.
      - exact (bincoprod_dep_assembly X₁ X₂).
      - exact (bincoprod_dep_assembly_inl X₁ X₂).
      - exact (bincoprod_dep_assembly_inr X₁ X₂).
      - intros Z f g.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros h₁ h₂ ;
             use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             use dep_assembly_morphism_eq ;
             intros x xy ;
             induction xy as [ y | y ] ;
             [ pose (dep_assembly_morphism_eq_point (pr12 h₁ @ pathsinv0 (pr12 h₂)) y)
               as q
             | pose (dep_assembly_morphism_eq_point (pr22 h₁ @ pathsinv0 (pr22 h₂)) y)
               as q ] ;
             exact (pathsinv0 (fiber_comp_dep_assembly _ _ _)
                    @ q
                    @ fiber_comp_dep_assembly _ _ _)).
        + simple refine (_ ,, _ ,, _). 
          * exact (bincoprod_dep_assembly_copair f g).
          * abstract
              (use dep_assembly_morphism_eq ;
               intros x xx ;
               apply fiber_comp_dep_assembly).
          * abstract
              (use dep_assembly_morphism_eq ;
               intros x xx ;
               apply fiber_comp_dep_assembly).
    Defined.
  End FixFiber.
    
  Definition fiberwise_initial_dep_assembly
    : fiberwise_initial (dep_assembly_cleaving A).
  Proof.
    split.
    - exact initial_dep_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         exact (left_adjoint_preserves_initial
                  _
                  (dep_assembly_dependent_products_type s))).
  Defined.

  Definition fiberwise_binproducts_dep_assembly
    : fiberwise_binproducts (dep_assembly_cleaving A).
  Proof.
    split.
    - exact binproducts_dep_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         apply (right_adjoint_preserves_binproduct
                  _
                  (is_left_adjoint_left_adjoint (assembly_dependent_sum_type s)))).
  Defined.

  Definition fiberwise_bincoproducts_dep_assembly
    : fiberwise_bincoproducts (dep_assembly_cleaving A).
  Proof.
    split.
    - exact bincoproducts_dep_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         exact (left_adjoint_preserves_bincoproduct
                  _
                  (dep_assembly_dependent_products_type s))).
  Defined.
End FiberStructure.
