(**

 Fiberwise structure for linear assemblies

 We show that the fiber categories of the fibration of linear assemblies comes with the
 following categorical structure:
 - initial object
 - binary products
 - binary coproducts
 In addition, we show that each fiber is a symmetric monoidal closed category.

 We also show that the substitution functors preserve all that structure. For the
 aforementioned limits and colimits this follows from the fact that we substitution has
 a left and a right adjoint. For the monoidal closed structure we show it by hand.

 Contents
 1. Fiberwise initial object
 2. Fiberwise binary products
 4. Fiberwise binary coproducts
 5. Fiberwise monoidal closed
 6. Preservation of fiberwise structure by substitution
 
 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

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
Require Import Types.LinearPi.

Local Open Scope lca.
Local Open Scope assembly.
Local Open Scope cat.

Section FiberStructureLinear.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  Section FixFiber.
    Context (Γ : assembly AC).

    Let Fib : category := (disp_cat_of_lin_dep_assembly A) [{Γ}].

    (** * 1. Fiberwise initial object *)
    Definition initial_obj_linear_assembly
      : dep_assembly Γ
      := λ x, initial_assembly A.

    Definition initial_linear_assembly_mor
               (X : dep_assembly Γ)
      : lin_dep_assembly_morphism
          initial_obj_linear_assembly
          X
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x, fromempty).
      - abstract
          (use hinhpr ;
           refine (I ,, _) ;
           intros x xx ;
           induction xx).
    Defined.
    
    Definition initial_linear_assembly
      : Initial Fib.
    Proof.
      use make_Initial.
      - exact initial_obj_linear_assembly.
      - intro X.
        use make_iscontr.
        + exact (initial_linear_assembly_mor X).
        + abstract
            (intro f ;
             use lin_dep_assembly_morphism_eq ;
             intros x xx ;
             induction xx).
    Defined.

    (** * 2. Fiberwise binary products *)
    Definition binprod_linear_assembly
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly Γ.
    Proof.
      intro x.
      use make_assembly.
      - exact (X₁ x × X₂ x)%set.
      - exact (λ a xy,
               ∃ (b c₁ c₂ : A),
               (a = lin_pair · b · (lin_pair · (!c₁) · (!c₂)))%lca
               × (c₁ · b)%lca ⊩ pr1 xy
               × (c₂ · b)%lca ⊩ pr2 xy).
      - abstract
          (intros ;
           apply propproperty).
      - abstract
          (intros (y₁ & y₂) ;
           pose proof (assembly_realizes_el y₁) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (b₁ & p₁) ;
           pose proof (assembly_realizes_el y₂) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (b₂ & p₂) ;
           use hinhpr ;
           refine (lin_pair · I · (lin_pair · (!(C · I · b₁)) · (!(C · I · b₂))) ,, _)%lca ;
           use hinhpr ;
           refine (I ,, C · I · b₁ ,, C · I · b₂ ,, _)%lca ;
           refine (idpath _ ,, _) ; simpl ;
           rewrite !linear_combinatory_algebra_c_eq ;
           rewrite !linear_combinatory_algebra_i_eq ;
           exact (p₁ ,, p₂)).
    Defined.

    Definition binprod_linear_assembly_pr1
               (X₁ X₂ : dep_assembly Γ)
      : lin_dep_assembly_morphism
          (binprod_linear_assembly X₁ X₂)
          X₁
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x xy, pr1 xy).
      - abstract
          (use hinhpr ;
           refine (lca_binprod_pr1 ,, _) ;
           intros x (y₁ & y₂) a₁ a₂ p ;
           use factor_through_squash_hProp ;
           intros (b & c₁ & c₂ & q₁ & q₂ & q₃) ;
           simpl in * ;
           rewrite q₁ ; clear q₁ ;
           rewrite lca_binprod_pr1_eq ;
           apply q₂).
    Defined.

    Definition binprod_linear_assembly_pr2
               (X₁ X₂ : dep_assembly Γ)
      : lin_dep_assembly_morphism
          (binprod_linear_assembly X₁ X₂)
          X₂
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x xy, pr2 xy).
      - abstract
          (use hinhpr ;
           refine (lca_binprod_pr2 ,, _) ;
           intros x (y₁ & y₂) a₁ a₂ p ;
           use factor_through_squash_hProp ;
           intros (b & c₁ & c₂ & q₁ & q₂ & q₃) ;
           simpl in * ;
           rewrite q₁ ; clear q₁ ;
           rewrite lca_binprod_pr2_eq ;
           apply q₃).
    Defined.

    Definition binprod_linear_assembly_pair
               {Z X₁ X₂ : dep_assembly Γ}
               (f : lin_dep_assembly_morphism Z X₁ (id_assembly_morphism _))
               (g : lin_dep_assembly_morphism Z X₂ (id_assembly_morphism _))
      : lin_dep_assembly_morphism
          Z
          (binprod_linear_assembly X₁ X₂)
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x z, f x z ,, g x z).
      - abstract
          (pose proof (lin_dep_assembly_morphism_function_track f) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a₁ & p₁) ;
           pose proof (lin_dep_assembly_morphism_function_track g) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a₂ & p₂) ;
           use hinhpr ;
           refine (lca_binprod_pair · (!a₁) · (!a₂) ,, _)%lca ;
           intros x xx b₁ b₂ q₁ q₂ ;
           use hinhpr ;
           simpl ;
           refine (b₂ ,, _) ;
           refine (a₁ · (!b₁) ,, a₂ · (!b₁) ,, _)%lca ;
           repeat split ;
           [
           | apply p₁ ; assumption
           | apply p₂ ; assumption ] ;
           rewrite lca_binprod_pair_eq ;
           apply idpath).
    Defined.

    Definition binproducts_linear_assembly
      : BinProducts Fib.
    Proof.
      intros X₁ X₂.
      use make_BinProduct.
      - exact (binprod_linear_assembly X₁ X₂).
      - exact (binprod_linear_assembly_pr1 X₁ X₂).
      - exact (binprod_linear_assembly_pr2 X₁ X₂).
      - intros Z f g.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros h₁ h₂ ;
             use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             use lin_dep_assembly_morphism_eq ;
             intros x xx ;
             pose (lin_dep_assembly_morphism_eq_point (pr12 h₁ @ pathsinv0 (pr12 h₂)) xx)
               as q₁ ;
             pose (lin_dep_assembly_morphism_eq_point (pr22 h₁ @ pathsinv0 (pr22 h₂)) xx)
               as q₂ ;
             pose (pathsinv0 (fiber_comp_lin_dep_assembly _ _ _)
                   @ q₁
                   @ fiber_comp_lin_dep_assembly _ _ _) as q₁' ;
             pose (pathsinv0 (fiber_comp_lin_dep_assembly _ _ _)
                   @ q₂
                   @ fiber_comp_lin_dep_assembly _ _ _) as q₂' ;
             exact (pathsdirprod q₁' q₂')).
        + simple refine (_ ,, _ ,, _). 
          * exact (binprod_linear_assembly_pair f g).
          * abstract
              (use lin_dep_assembly_morphism_eq ;
               intros x xx ;
               apply fiber_comp_lin_dep_assembly).
          * abstract
              (use lin_dep_assembly_morphism_eq ;
               intros x xx ;
               apply fiber_comp_lin_dep_assembly).
    Defined.

    (** * 3. Fiberwise equalizers *)
    Definition equalizer_linear_assembly
               {X₁ X₂ : dep_assembly Γ}
               (f g : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism _))
      : dep_assembly Γ.
    Proof.
      intro γ.
      use make_assembly.
      - use make_hSet.
        + exact (∑ (x : X₁ γ), f γ x = g γ x).
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

    Definition equalizer_linear_assembly_pr
               {X₁ X₂ : dep_assembly Γ}
               (f g : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism _))
      : lin_dep_assembly_morphism
          (equalizer_linear_assembly f g)
          X₁
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ γ x, pr1 x).
      - abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros γ x a₁ a₂ p₁ p₂ ;
           rewrite linear_combinatory_algebra_ks_eq ;
           exact p₂).
    Defined.

    Definition equalizer_linear_assembly_mor
               {X' X₁ X₂ : dep_assembly Γ}
               (f g : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism _))
               (h : lin_dep_assembly_morphism X' X₁ (id_assembly_morphism _))
               (p : fiber_comp_lin_dep_assembly_morphism h f
                    =
                    fiber_comp_lin_dep_assembly_morphism h g)
      : lin_dep_assembly_morphism
          X'
          (equalizer_linear_assembly f g)
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - refine (λ γ x, h γ x ,, _).
        abstract
          (exact (pathsinv0 (fiber_comp_lin_dep_assembly _ _ _)
                  @ lin_dep_assembly_morphism_eq_point p x
                  @ fiber_comp_lin_dep_assembly _ _ _)).
      - abstract
          (pose proof (lin_dep_assembly_morphism_function_track h) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros (a & q) ;
           use hinhpr ;
           refine (a ,, _) ;
           intros γ x b₁ b₂ r₁ r₂ ; simpl ;
           exact (q _ _ _ _ r₁ r₂)).
    Defined.
    
    Definition equalizers_linear_assembly
      : Equalizers Fib.
    Proof.
      intros X₁ X₂ f g.
      use make_Equalizer.
      - exact (equalizer_linear_assembly f g).
      - exact (equalizer_linear_assembly_pr f g).
      - abstract
          (use lin_dep_assembly_morphism_eq ;
           intros γ x ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           refine (_ @ pathsinv0 (fiber_comp_lin_dep_assembly _ _ _)) ;
           cbn ;
           exact (pr2 x)).
      - intros X' h p.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ; [ intro ; apply homset_property | ] ;
             use lin_dep_assembly_morphism_eq ;
             intros γ x ;
             use subtypePath ; [ intro ; apply setproperty | ] ;
             exact (pathsinv0 (fiber_comp_lin_dep_assembly _ _ _)
                    @ lin_dep_assembly_morphism_eq_point (pr2 φ₁ @ pathsinv0 (pr2 φ₂)) x
                    @ fiber_comp_lin_dep_assembly _ _ _)).
        + simple refine (_ ,, _).
          * exact (equalizer_linear_assembly_mor f g h p).
          * abstract
              (use lin_dep_assembly_morphism_eq ;
               intros γ x ;
               exact (fiber_comp_lin_dep_assembly _ _ _)).
    Defined.
               
    (** * 4. Fiberwise binary coproducts *)
    Definition bincoprod_linear_assembly
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly Γ.
    Proof.
      intro x.
      use make_assembly.
      - exact (setcoprod (X₁ x) (X₂ x))%set.
      - intros a xy.
        destruct xy as [ y₁ | y₂ ].
        + exact (∃ (b : A),
                 a = lin_pair · lca_bincoprod_left · b
                 ×
                 b ⊩ y₁)%lca.
        + exact (∃ (b : A),
                 a = lin_pair · lca_bincoprod_right · b
                 ×
                 b ⊩ y₂)%lca.
      - abstract
          (intros a [ y₁ | y₂ ];
           apply propproperty).
      - abstract
          (intros y ; induction y as [ y | y ] ;
           pose proof (assembly_realizes_el y) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a & p) ;
           use hinhpr ;
           refine (lin_pair · _ · a ,, _)%lca ;
           use hinhpr ;
           refine (a ,, _) ;
           exact (idpath _ ,, p)).
    Defined.

    Definition bincoprod_linear_assembly_inl
               (X₁ X₂ : dep_assembly Γ)
      : lin_dep_assembly_morphism
          X₁
          (bincoprod_linear_assembly X₁ X₂)
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x xy, inl xy).
      - abstract
          (use hinhpr ;
           refine (lca_bincoprod_inl ,, _) ;
           intros x xx a₁ a₂ p₁ p₂ ;
           use hinhpr ;
           refine (a₂ ,, _) ;
           rewrite lca_bincoprod_inl_eq ;
           exact (idpath _ ,, p₂)).
    Defined.

    Definition bincoprod_linear_assembly_inr
               (X₁ X₂ : dep_assembly Γ)
      : lin_dep_assembly_morphism
          X₂
          (bincoprod_linear_assembly X₁ X₂)
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x xy, inr xy).
      - abstract
          (use hinhpr ;
           refine (lca_bincoprod_inr ,, _) ;
           intros x xx a₁ a₂ p₁ p₂ ;
           use hinhpr ;
           refine (a₂ ,, _) ;
           rewrite lca_bincoprod_inr_eq ;
           exact (idpath _ ,, p₂)).
    Defined.

    Definition bincoprod_linear_assembly_copair_map
               {X₁ X₂ Z : dep_assembly Γ}
               (f : lin_dep_assembly_morphism X₁ Z (id_assembly_morphism _))
               (g : lin_dep_assembly_morphism X₂ Z (id_assembly_morphism _))
               (x : Γ)
               (xy : bincoprod_linear_assembly X₁ X₂ x)
      : Z x.
    Proof.
      induction xy as [ y | y ].
      - exact (f x y).
      - exact (g x y).
    Defined.

    Proposition bincoprod_linear_assembly_copair_tracker
                {X₁ X₂ Z : dep_assembly Γ}
                (f : lin_dep_assembly_morphism X₁ Z (id_assembly_morphism _))
                (g : lin_dep_assembly_morphism X₂ Z (id_assembly_morphism _))
      : lin_dep_assembly_morphism_tracker
          (s := id_assembly_morphism _)
          (bincoprod_linear_assembly_copair_map f g).
    Proof.
      pose proof (lin_dep_assembly_morphism_function_track f) as p.
      revert p.
      use factor_through_squash_hProp.
      intros (a₁ & p₁).
      pose proof (lin_dep_assembly_morphism_function_track g) as p.
      revert p.
      use factor_through_squash_hProp.
      intros (a₂ & p₂).
      use hinhpr.
      refine (lca_bincoprod_map · (!a₁) · (!a₂) ,, _)%lca.
      intros x xy.
      induction xy as [ y | y ].
      - intros b₁ b₂ q.
        use factor_through_squash_hProp.
        intros (c & r₁ & r₂).
        simpl.
        rewrite r₁.
        rewrite lca_bincoprod_map_eq.
        rewrite lca_bincoprod_left_eq.
        apply p₁.
        + exact q.
        + exact r₂.
      - intros b₁ b₂ q.
        use factor_through_squash_hProp.
        intros (c & r₁ & r₂).
        simpl.
        rewrite r₁.
        rewrite lca_bincoprod_map_eq.
        rewrite lca_bincoprod_right_eq.
        apply p₂.
        + exact q.
        + exact r₂.
    Qed.
    
    Definition bincoprod_linear_assembly_copair
               {X₁ X₂ Z : dep_assembly Γ}
               (f : lin_dep_assembly_morphism X₁ Z (id_assembly_morphism _))
               (g : lin_dep_assembly_morphism X₂ Z (id_assembly_morphism _))
      : lin_dep_assembly_morphism
          (bincoprod_linear_assembly X₁ X₂)
          Z
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (bincoprod_linear_assembly_copair_map f g).
      - exact (bincoprod_linear_assembly_copair_tracker f g).
    Defined.

    Definition bincoproducts_linear_assembly
      : BinCoproducts Fib.
    Proof.
      intros X₁ X₂.
      use make_BinCoproduct.
      - exact (bincoprod_linear_assembly X₁ X₂).
      - exact (bincoprod_linear_assembly_inl X₁ X₂).
      - exact (bincoprod_linear_assembly_inr X₁ X₂).
      - intros Z f g.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros h₁ h₂ ;
             use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             use lin_dep_assembly_morphism_eq ;
             intros x xy ;
             induction xy as [ y | y ] ;
             [ pose (lin_dep_assembly_morphism_eq_point (pr12 h₁ @ pathsinv0 (pr12 h₂)) y)
               as q
             | pose (lin_dep_assembly_morphism_eq_point (pr22 h₁ @ pathsinv0 (pr22 h₂)) y)
               as q ] ;
             exact (pathsinv0 (fiber_comp_lin_dep_assembly _ _ _)
                    @ q
                    @ fiber_comp_lin_dep_assembly _ _ _)).
        + simple refine (_ ,, _ ,, _). 
          * exact (bincoprod_linear_assembly_copair f g).
          * abstract
              (use lin_dep_assembly_morphism_eq ;
               intros x xx ;
               apply fiber_comp_lin_dep_assembly).
          * abstract
              (use lin_dep_assembly_morphism_eq ;
               intros x xx ;
               apply fiber_comp_lin_dep_assembly).
    Defined.

    (** * 5. Fiberwise monoidal closed *)
    Definition tracks_linear_assembly_fiber_function
               {X₁ X₂ : dep_assembly Γ}
               {x : Γ}
               (f : X₁ x → X₂ x)
               (a : A)
      : UU
      := ∏ (y : X₁ x)
           (b : A),
         b ⊩ y → (a · b)%lca ⊩ f y.

    Proposition isaprop_tracks_linear_assembly_fiber_function
                {X₁ X₂ : dep_assembly Γ}
                {x : Γ}
                (f : X₁ x → X₂ x)
                (a : A)
      : isaprop (tracks_linear_assembly_fiber_function f a).
    Proof.
      repeat (use impred ; intro).
      apply propproperty.
    Qed.
    
    Definition linear_assembly_fiber_function
               (X₁ X₂ : dep_assembly Γ)
               (x : Γ)
      : UU
      := ∑ (f : X₁ x → X₂ x),
         ∃ (a : A), tracks_linear_assembly_fiber_function f a.

    Definition make_linear_assembly_fiber_function
               {X₁ X₂ : dep_assembly Γ}
               {x : Γ}
               (f : X₁ x → X₂ x)
               (p : ∃ (a : A), tracks_linear_assembly_fiber_function f a)
      : linear_assembly_fiber_function X₁ X₂ x
      := f ,, p.
    
    Proposition isaset_linear_assembly_fiber_function
                (X₁ X₂ : dep_assembly Γ)
                (x : Γ)
      : isaset (linear_assembly_fiber_function X₁ X₂ x).
    Proof.
      use isaset_total2.
      - use funspace_isaset.
        apply setproperty.
      - intro.
        apply isasetaprop.
        apply propproperty.
    Qed.
                
    Definition linear_assembly_fiber_function_to_fun
               {X₁ X₂ : dep_assembly Γ}
               {x : Γ}
               (f : linear_assembly_fiber_function X₁ X₂ x)
               (y : X₁ x)
      : X₂ x
      := pr1 f y.

    Coercion linear_assembly_fiber_function_to_fun
      : linear_assembly_fiber_function >-> Funclass.

    Definition linear_assembly_fiber_function_tracker
               {X₁ X₂ : dep_assembly Γ}
               {x : Γ}
               (f : linear_assembly_fiber_function X₁ X₂ x)
      : ∃ (a : A), tracks_linear_assembly_fiber_function f a
      := pr2 f.

    Proposition linear_assembly_fiber_function_eq
                {X₁ X₂ : dep_assembly Γ}
                {x : Γ}
                {f g : linear_assembly_fiber_function X₁ X₂ x}
                (p : ∏ (y : X₁ x), f y = g y)
      : f = g.
    Proof.
      use subtypePath.
      {
        intro.
        apply propproperty.
      }
      use funextsec.
      exact p.
    Qed.
               
    Definition linear_assembly_functions
               (X₁ X₂ : dep_assembly Γ)
      : dep_assembly Γ.
    Proof.
      intro x.
      use make_assembly.
      - use make_hSet.
        + exact (linear_assembly_fiber_function X₁ X₂ x).
        + apply isaset_linear_assembly_fiber_function.
      - exact (λ a f, tracks_linear_assembly_fiber_function (pr1 f) a).
      - abstract
          (intros ;
           apply isaprop_tracks_linear_assembly_fiber_function).
      - intro f.
        exact (linear_assembly_fiber_function_tracker f).
    Defined.

    Definition linear_assembly_eval
               (X₁ X₂ : dep_assembly Γ)
      : lin_dep_assembly_morphism
          (monoidal_product_lin_dep_assembly
             (linear_assembly_functions X₁ X₂)
             X₁)
          X₂
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ (x : Γ)
                 (fy : linear_assembly_fiber_function _ _ _ × X₁ x),
               pr1 fy (pr2 fy)).
      - abstract
          (use hinhpr ;
           refine (lca_eval ,, _) ;
           intros x (f & y) a₁ a₂ p ;
           use factor_through_squash_hProp ;
           intros (b₁ & b₂ & q₁ & q₂ & q₃) ; simpl in * ;
           rewrite q₃ ; clear a₂ q₃ ;
           specialize (q₁ y b₂ q₂) ;
           rewrite lca_eval_eq ;
           exact q₁).
    Defined.

    Section Lambda.
      Context {X₁ X₂ Z : dep_assembly Γ}
              (f : lin_dep_assembly_morphism
                     (monoidal_product_lin_dep_assembly Z X₁)
                     X₂
                     (id_assembly_morphism _)).

      Proposition linear_assembly_lam_pt_tracker
                  {x : Γ}
                  (z : Z x)
        : ∃ (a : A),
          tracks_linear_assembly_fiber_function (λ y : X₁ x, f x (z,, y)) a.
      Proof.
        pose proof (lin_dep_assembly_morphism_function_track f) as p.
        revert p.
        use factor_through_squash_hProp.
        intros (a & p).
        pose proof (assembly_realizes_el z) as q.
        revert q.
        use factor_through_squash_hProp.
        intros (b & q).
        pose proof (assembly_realizes_el x) as q'.
        revert q'.
        use factor_through_squash_hProp.
        intros (b' & q').
        use hinhpr.
        refine ((lca_lam_pt · a · b · !b')%lca ,, _).
        intros y c r.
        specialize (p x (z ,, y) b' (lin_pair · b · c)%lca q').
        rewrite lca_lam_pt_eq.
        apply p.
        use hinhpr ; simpl.
        refine (b ,, c ,, _).
        repeat split ; assumption.
      Qed.
      
      Definition linear_assembly_lam_pt
                 {x : Γ}
                 (z : Z x)
        : linear_assembly_fiber_function X₁ X₂ x.
      Proof.
        use make_linear_assembly_fiber_function.
        - exact (λ y, f x (z ,, y)).
        - exact (linear_assembly_lam_pt_tracker z).
      Defined.

      Proposition linear_assembly_lam_tracker
        : lin_dep_assembly_morphism_tracker
            (X₁ := Z)
            (X₂ := linear_assembly_functions X₁ X₂)
            (s := id_assembly_morphism _)
            (λ (x : Γ) (z : Z x), linear_assembly_lam_pt z).
      Proof.
        pose proof (lin_dep_assembly_morphism_function_track f) as p.
        revert p.
        use factor_through_squash_hProp.
        intros (a & p).
        use hinhpr.
        refine ((lca_lam · a)%lca ,, _).
        intros x z b₁ b₂ q₁ q₂ y c r.
        simpl in *.
        rewrite lca_lam_eq.
        specialize (p x (z ,, y) b₁ (lin_pair · b₂ · c)%lca q₁).
        apply p.
        use hinhpr ; simpl.
        refine (b₂ ,, c ,, _).
        repeat split ; assumption.
      Qed.
      
      Definition linear_assembly_lam
        : lin_dep_assembly_morphism
            Z
            (linear_assembly_functions X₁ X₂)
            (id_assembly_morphism _).
      Proof.
        use make_lin_dep_assembly_morphism.
        - exact (λ x z, linear_assembly_lam_pt z).
        - exact linear_assembly_lam_tracker.
      Defined.
    End Lambda.

    Definition linear_assembly_sym_mon_closed_cat
      : sym_mon_closed_cat.
    Proof.
      use make_sym_mon_closed_cat.
      - exact (fiber_sym_monoidal_cat fiberwise_symmetric_monoidal_lin_dep_assembly Γ).
      - exact linear_assembly_functions.
      - exact linear_assembly_eval.
      - exact @linear_assembly_lam.
      - abstract
          (intros X₁ X₂ X₃ f ;
           use lin_dep_assembly_morphism_eq ;
           intros x y ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           etrans ;
           [ apply maponpaths ;
             refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ; cbn ;
             apply idpath
           | ] ;
           cbn ;
           apply idpath).
      - abstract
          (intros X₁ X₂ X₃ f ;
           use lin_dep_assembly_morphism_eq ;
           intros x y ;
           use linear_assembly_fiber_function_eq ;
           intros y' ;
           simpl ;
           apply pathsinv0 ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           etrans ;
           [ apply maponpaths ;
             refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ; cbn ;
             apply idpath
           | ] ;
           apply idpath).
    Defined.

    Proposition linear_assembly_internal_lam
                {X₁ X₂ Z : dep_assembly Γ}
                (f : lin_dep_assembly_morphism
                       (monoidal_product_lin_dep_assembly Z X₁)
                       X₂
                       (id_assembly_morphism _))
                {x : Γ}
                (z : Z x)
                (y : X₁ x)
      : pr1 (pr1 (internal_lam (V := linear_assembly_sym_mon_closed_cat) f) x z) y
        =
        f x (z ,, y).
    Proof.
      unfold internal_lam.
      cbn -[fiber_category].
      etrans.
      {
        apply maponpaths_2.
        exact (fiber_comp_lin_dep_assembly (linear_assembly_lam _) (linear_assembly_lam _) _).
      }
      refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      cbn.
      apply idpath.
    Qed.
  End FixFiber.

  (** * 6. Preservation of fiberwise structure by substitution *)
  Definition preserves_sym_mon_closed_lin_assembly_fiber_functor
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : @preserves_sym_mon_closed
         (linear_assembly_sym_mon_closed_cat Γ₂)
         (linear_assembly_sym_mon_closed_cat Γ₁)
         (strong_sym_monoidal_fiber_functor
            fiberwise_symmetric_monoidal_lin_dep_assembly
            s).
  Proof.
    intros X₁ X₂.
    use make_is_z_isomorphism.
    - use make_lin_dep_assembly_morphism.
      + cbn in *.
        intros x f.
        use make_linear_assembly_fiber_function.
        * exact f.
        * abstract (apply f).
      + abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x f a₁ a₂ p₁ p₂ ;
           cbn in * ;
           rewrite linear_combinatory_algebra_ks_eq ;
           exact p₂).
    - split.
      + abstract
          (use lin_dep_assembly_morphism_eq ;
           intros x f ; cbn in f ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           use linear_assembly_fiber_function_eq ;
           intros y ; cbn in y ;
           cbn -[fiber_category] ;
           unfold preserves_sym_mon_closed_map ;
           cbn -[fiber_category strong_sym_monoidal_fiber_functor] ;
           refine (linear_assembly_internal_lam _ _ _ _ @ _) ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           cbn -[fiber_functor_from_cleaving] ;
           refine (fiber_functor_from_cleaving_lin_dep_assembly s _ _ @ _) ;
           cbn ;
           apply idpath).
      + abstract
          (use lin_dep_assembly_morphism_eq ;
           intros x f ; cbn in f ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           use linear_assembly_fiber_function_eq ;
           intros y ; cbn in y ;
           cbn -[fiber_category] ;
           unfold preserves_sym_mon_closed_map ;
           cbn -[fiber_category strong_sym_monoidal_fiber_functor] ;
           refine (linear_assembly_internal_lam _ _ _ _ @ _) ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           cbn -[fiber_functor_from_cleaving] ;
           refine (fiber_functor_from_cleaving_lin_dep_assembly s _ _ @ _) ;
           cbn ;
           apply idpath).
  Defined.

  Definition fiberwise_initial_lin_dep_assembly
    : fiberwise_initial (lin_dep_assembly_cleaving A).
  Proof.
    split.
    - exact initial_linear_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         exact (left_adjoint_preserves_initial
                  _
                  (pr1 lin_dep_assembly_dependent_products _ _ s))).
  Defined.

  Definition fiberwise_binproducts_lin_dep_assembly
    : fiberwise_binproducts (lin_dep_assembly_cleaving A).
  Proof.
    split.
    - exact binproducts_linear_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         apply (right_adjoint_preserves_binproduct
                  _
                  (is_left_adjoint_left_adjoint (pr1 lin_dep_assembly_dependent_sums _ _ s)))).
  Defined.

  Definition fiberwise_equalizers_lin_dep_assembly
    : fiberwise_equalizers (lin_dep_assembly_cleaving A).
  Proof.
    split.
    - exact equalizers_linear_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         apply (right_adjoint_preserves_equalizer
                  _
                  (is_left_adjoint_left_adjoint (pr1 lin_dep_assembly_dependent_sums _ _ s)))).
  Defined.

  Definition fiberwise_bincoproducts_lin_dep_assembly
    : fiberwise_bincoproducts (lin_dep_assembly_cleaving A).
  Proof.
    split.
    - exact bincoproducts_linear_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         exact (left_adjoint_preserves_bincoproduct
                  _
                  (pr1 lin_dep_assembly_dependent_products _ _ s))).
  Defined.
End FiberStructureLinear.
