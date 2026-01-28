(**

 The linear-non linear adjunction

 Given a linear combinatory algebra `A`, we construct the linear-non linear adjunction
 between assemblies over `A` (linear part) and assemblies over the associated combinatory
 algebra `A_!` (Cartesian part). We prove the following facts about this adjunction:
 - It is a fibered adjunction meaning that the involved functors are Cartesian
 - It is a symmetric monoidal adjunction. For this it is sufficient to show that the left
   adjoint is a strong symmetric monoidal functor.
 - We also prove an isomorphism for terms necessary to interpret dependent linear logic
   (see Definition 4.20 in 'Models of linear dependent type theory' by Lundfall)

 Contents
 1. From linear to Cartesian
 2. From Cartesian to linear
 2.1. This functor is strong monoidal
 2.2. This functor is Cartesian
 3. The unit and counit
 4. The adjunction
 5. An isomorphism for terms

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Require Import Basics.BIAlgebra.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Combinators.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Assemblies.LinearAssemblyMonoidal.
Require Import Types.LinearFiber.
Require Import Types.FiberAssembly.

Local Open Scope lca.
Local Open Scope assembly.
Local Open Scope cat.

Section LinearNonLinearAssembly.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  (** * 1. From linear to Cartesian *)
  Definition lin_dep_to_dep_assembly_morphism
             {Γ₁ Γ₂ : assembly AC}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : lin_dep_assembly_morphism X₁ X₂ s)
    : dep_assembly_morphism X₁ X₂ s.
  Proof.
    use make_dep_assembly_morphism.
    - exact (λ x y, f x y).
    - abstract
        (pose proof (lin_dep_assembly_morphism_function_track f) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros (a & p) ;
         use hinhpr ;
         refine ((lca_del_2 · a)%lca ,, _) ; cbn ; cbn in p ;
         intros x xx b₁ b₂ p₁ p₂ ;
         rewrite lca_del_2_eq ;
         apply p ; cbn ; assumption).
  Defined.

  Proposition lin_dep_to_dep_assembly_morphism_faithful
              {Γ₁ Γ₂ : assembly AC}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              {f g : lin_dep_assembly_morphism X₁ X₂ s}
              (p : lin_dep_to_dep_assembly_morphism f
                   =
                   lin_dep_to_dep_assembly_morphism g)
    : f = g.
  Proof.
    use lin_dep_assembly_morphism_eq.
    intros x xx.
    exact (dep_assembly_morphism_eq_point p xx).
  Qed.
  
  Definition lin_to_dep_assembly_data
    : disp_functor_data
        (functor_identity _)
        (disp_cat_of_lin_dep_assembly A)
        (disp_cat_of_dep_assembly AC).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ X, X).
    - exact (λ Γ₁ Γ₂ X₁ X₂ s f, lin_dep_to_dep_assembly_morphism f).
  Defined.

  Proposition lin_to_dep_assembly_laws
    : disp_functor_axioms lin_to_dep_assembly_data.
  Proof.
    split.
    - intros Γ X.
      use dep_assembly_morphism_eq.
      intros x xx.
      apply pathsinv0.
      etrans.
      {
        apply transportb_dep_assembly_mor.
      }
      cbn.
      apply idpath.
    - intros Γ₁ Γ₂ Γ₃ X₁ X₂ X₃ s₁ s₂ f g.
      use dep_assembly_morphism_eq.
      intros x xx.
      apply pathsinv0.
      etrans.
      {
        apply transportb_dep_assembly_mor.
      }
      cbn.
      apply idpath.
  Qed.
  
  Definition lin_to_dep_assembly
    : disp_functor
        (functor_identity _)
        (disp_cat_of_lin_dep_assembly A)
        (disp_cat_of_dep_assembly AC).
  Proof.
    simple refine (_ ,, _).
    - exact lin_to_dep_assembly_data.
    - exact lin_to_dep_assembly_laws.
  Defined.

  Definition is_cartesian_lin_to_dep_assembly
    : is_cartesian_disp_functor lin_to_dep_assembly.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact (lin_dep_assembly_cleaving A).
    }
    cbn.
    intros Γ₁ Γ₂ s X.
    refine (transportf
              is_cartesian
              _
              (is_cartesian_dep_assembly_subst_mor (A := AC) s X)).
    use dep_assembly_morphism_eq.
    intros x xx ; cbn.
    apply idpath.
  Qed.

  (** * 2. From Cartesian to linear *)
  Definition excl_lin_assembly
             {Γ : assembly AC}
             (X : dep_assembly Γ)
    : dep_assembly Γ.
  Proof.
    refine (λ x, _).
    use make_assembly.
    - exact (X x).
    - exact (λ a xx, ∃ (b : A), a = !b × b ⊩ xx).
    - abstract
        (intros ;
         apply propproperty).
    - abstract
        (intro xx ;
         pose proof (assembly_realizes_el xx) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros (a & p) ;
         use hinhpr ;
         refine (!a ,, _) ;
         use hinhpr ;
         refine (a ,, _) ;
         exact (idpath _ ,, p)).
  Defined.

  Definition dep_to_lin_dep_assembly_morphism
             {Γ₁ Γ₂ : assembly AC}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : dep_assembly_morphism X₁ X₂ s)
    : lin_dep_assembly_morphism
        (excl_lin_assembly X₁)
        (excl_lin_assembly X₂)
        s.
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x y, f x y).
    - abstract
        (pose proof (dep_assembly_morphism_function_track f) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros (a & p) ; cbn in p ;
         use hinhpr ;
         refine ((lca_F_2 · !a)%lca ,, _) ;
         intros x xx b₁ b₂ q ;
         use factor_through_squash_hProp ;
         intros (c & r₁ & r₂) ;
         rewrite r₁ ; clear r₁ ;
         specialize (p x xx b₁ c q r₂) ;
         use hinhpr ;
         refine ((a · b₁ · c)%lca ,, _) ;
         rewrite lca_F_2_eq ;
         refine (idpath _ ,, _) ;
         exact p).
  Defined.

  Proposition dep_to_lin_dep_assembly_morphism_faithful
              {Γ₁ Γ₂ : assembly AC}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              {f g : dep_assembly_morphism X₁ X₂ s}
              (p : dep_to_lin_dep_assembly_morphism f
                   =
                   dep_to_lin_dep_assembly_morphism g)
    : f = g.
  Proof.
    use dep_assembly_morphism_eq.
    intros x xx.
    exact (lin_dep_assembly_morphism_eq_point p xx).
  Qed.
             
  Definition dep_to_lin_assembly_data
    : disp_functor_data
        (functor_identity _)
        (disp_cat_of_dep_assembly AC)
        (disp_cat_of_lin_dep_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ X, excl_lin_assembly X).
    - exact (λ Γ₁ Γ₂ X₁ X₂ s f, dep_to_lin_dep_assembly_morphism f).
  Defined.

  Proposition dep_to_lin_assembly_laws
    : disp_functor_axioms dep_to_lin_assembly_data.
  Proof.
    split.
    - intros Γ X.
      use lin_dep_assembly_morphism_eq.
      intros x xx.
      apply pathsinv0.
      etrans.
      {
        apply transportb_lin_dep_assembly_mor.
      }
      cbn.
      apply idpath.
    - intros Γ₁ Γ₂ Γ₃ X₁ X₂ X₃ s₁ s₂ f g.
      use lin_dep_assembly_morphism_eq.
      intros x xx.
      apply pathsinv0.
      etrans.
      {
        apply transportb_lin_dep_assembly_mor.
      }
      cbn.
      apply idpath.
  Qed.

  Definition dep_to_lin_assembly
    : disp_functor
        (functor_identity _)
        (disp_cat_of_dep_assembly AC)
        (disp_cat_of_lin_dep_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact dep_to_lin_assembly_data.
    - exact dep_to_lin_assembly_laws.
  Defined.

  (** * 2.1. This functor is strong monoidal *)
  Definition fiber_functor_dep_to_lin_tensor
             {Γ : assembly AC}
             (X₁ X₂ : dep_assembly Γ)
    : lin_dep_assembly_morphism
        (monoidal_product_lin_dep_assembly
           (excl_lin_assembly X₁)
           (excl_lin_assembly X₂))
        (excl_lin_assembly (binprod_dep_assembly Γ X₁ X₂))
        (id_assembly_morphism _).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, xx).
    - abstract
        (use hinhpr ; simpl ;
         refine (lin_pair_to_pair ,, _)%lca ;
         intros x xx a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
         revert q₁ ;
         use factor_through_squash_hProp ;
         intros (c & r & r₁) ;
         rewrite r in * ; clear b₁ r ;
         revert q₂ ;
         use factor_through_squash_hProp ;
         intros (c' & r & r₂) ;
         rewrite r in * ; clear b₂ r ;
         rewrite q₃ ; clear a₂ q₃ ;
         use hinhpr ;
         refine (((pair : AC) · c · c')%ca ,, _) ;
         cbn -[lca_to_ca_applicative] ;
         rewrite (combinatory_algebra_pr1_pair (A := AC)) ;
         rewrite (combinatory_algebra_pr2_pair (A := AC)) ;
         rewrite lin_pair_to_pair_eq ;
         exact (idpath _ ,, r₁ ,, r₂)).
  Defined.

  Proposition fiber_functor_dep_to_lin_tensor_inv_tracker
             {Γ : assembly AC}
             (X₁ X₂ : dep_assembly Γ)
    : lin_dep_assembly_morphism_tracker
        (X₁ := excl_lin_assembly (binprod_dep_assembly Γ X₁ X₂))
        (X₂ := monoidal_product_lin_dep_assembly
           (excl_lin_assembly X₁)
           (excl_lin_assembly X₂))
        (s := id_assembly_morphism _)
        (λ x xx, xx).
  Proof.
    use hinhpr ; simpl.
    refine (to_lin_pair_proj ,, _).
    intros x [ y₁ y₂ ] a₁ a₂ p.
    use factor_through_squash_hProp.
    intros (b & q₁ & q₂ & q₃).
    simpl in q₂, q₃.
    rewrite q₁ ; clear a₂ q₁.
    use hinhpr.
    refine (!((π₁ : AC)%ca · b) ,, !((π₂ : AC)%ca · b) ,, _)%lca.
    repeat split.
    - use hinhpr.
      refine ((π₁ : AC)%ca · b ,, _)%lca.
      refine (idpath _ ,, _).
      exact q₂.
    - use hinhpr.
      refine ((π₂ : AC)%ca · b ,, _)%lca.
      refine (idpath _ ,, _).
      exact q₃.
    - rewrite to_lin_pair_proj_eq.
      apply idpath.
  Qed.
  
  Definition fiber_functor_dep_to_lin_tensor_inv
             {Γ : assembly AC}
             (X₁ X₂ : dep_assembly Γ)
    : lin_dep_assembly_morphism
        (excl_lin_assembly (binprod_dep_assembly Γ X₁ X₂))
        (monoidal_product_lin_dep_assembly
           (excl_lin_assembly X₁)
           (excl_lin_assembly X₂))
        (id_assembly_morphism _).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, xx).
    - exact (fiber_functor_dep_to_lin_tensor_inv_tracker X₁ X₂).
  Defined.

  Definition fiber_functor_dep_to_lin_unit
             (Γ : assembly AC)
    : lin_dep_assembly_morphism
        (unit_dep_assembly Γ)
        (excl_lin_assembly (terminal_dep_assembly _))
        (id_assembly_morphism _).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ _ _, tt).
    - abstract
        (use hinhpr ;
         refine (C · I ,, _)%lca ;
         intros x ? b₁ b₂ p₁ p₂ ;
         use hinhpr ;
         cbn in * ;
         rewrite p₂ ;
         clear b₂ p₂ ;
         refine (b₁ ,, _ ,, tt) ;
         rewrite linear_combinatory_algebra_c_eq ;
         rewrite !linear_combinatory_algebra_i_eq ;
         apply idpath).
  Defined.

  Definition fiber_functor_dep_to_lin_unit_inv
             (Γ : assembly AC)
    : lin_dep_assembly_morphism
        (excl_lin_assembly (terminal_dep_assembly _))
        (unit_dep_assembly Γ)
        (id_assembly_morphism _).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ _ _, tt).
    - abstract
        (use hinhpr ;
         refine (lca_k_I ,, _) ;
         intros x [] a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (b & q₁ & q₂) ;
         simpl in * ;
         rewrite q₁ ; clear a₂ q₁ ;
         rewrite lca_k_I_eq ;
         apply idpath).
  Defined.
  
  Definition fiber_functor_dep_to_lin_monoidal_data
             (Γ : assembly AC)
    : fmonoidal_data
        (dependent_assembly_cartesian_monoidalcat _)
        (linear_assembly_sym_mon_closed_cat _)
        (fiber_functor dep_to_lin_assembly Γ).
  Proof.
    split.
    - exact fiber_functor_dep_to_lin_tensor.
    - exact (fiber_functor_dep_to_lin_unit Γ).
  Defined.

  Proposition fiber_functor_dep_to_lin_monoidal_lax_laws
              (Γ : assembly AC)
    : fmonoidal_laxlaws (fiber_functor_dep_to_lin_monoidal_data Γ).
  Proof.
    repeat split ; intro ; intros ; use lin_dep_assembly_morphism_eq ; intros ? xx.
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      apply pathsinv0.
      refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      cbn -[fiber_category].
      apply pathsdirprod.
      + exact (fiber_comp_dep_assembly _ _ _).
      + exact (fiber_comp_dep_assembly _ _ _).
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      apply pathsinv0.
      refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      cbn -[fiber_category].
      apply pathsdirprod.
      + exact (fiber_comp_dep_assembly _ _ _).
      + exact (fiber_comp_dep_assembly _ _ _).
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      apply pathsinv0.
      refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lassociator
                    (excl_lin_assembly _)
                    (excl_lin_assembly _)
                    (excl_lin_assembly _))
                 (lwhisker_lin_dep_assembly
                    _
                    (fiber_functor_dep_to_lin_tensor _ _))
                 xx).
      }
      cbn -[fiber_category].
      repeat apply pathsdirprod.
      + apply pathsinv0.
        refine (fiber_comp_dep_assembly _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths.
          exact (fiber_comp_lin_dep_assembly
                   _
                   (fiber_functor_dep_to_lin_tensor (binprod_dep_assembly _ _ _) _)
                   xx).
        }
        cbn.
        apply idpath.
      + apply pathsinv0.
        refine (fiber_comp_dep_assembly _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths.
          exact (fiber_comp_lin_dep_assembly
                   _
                   (fiber_functor_dep_to_lin_tensor (binprod_dep_assembly _ _ _) _)
                   xx).
        }
        cbn.
        apply idpath.
      + apply pathsinv0.
        etrans.
        {
          apply maponpaths.
          exact (fiber_comp_lin_dep_assembly
                   _
                   (fiber_functor_dep_to_lin_tensor (binprod_dep_assembly _ _ _) _)
                   xx).
        }
        cbn.
        apply idpath.
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      cbn -[fiber_category].
      etrans.
      {
        apply maponpaths.
        exact (fiber_comp_lin_dep_assembly
                  _
                  (fiber_functor_dep_to_lin_tensor _ _)
                  _).
      }
      cbn.
      apply idpath.
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      cbn -[fiber_category].
      etrans.
      {
        apply maponpaths.
        exact (fiber_comp_lin_dep_assembly
                  _
                  (fiber_functor_dep_to_lin_tensor _ _)
                  _).
      }
      cbn.
      apply idpath.
  Qed.
      
  Definition fiber_functor_dep_to_lin_monoidal_lax
             (Γ : assembly AC)
    : fmonoidal_lax
        (dependent_assembly_cartesian_monoidalcat _)
        (linear_assembly_sym_mon_closed_cat _)
        (fiber_functor dep_to_lin_assembly Γ).
  Proof.
    simple refine (_ ,, _).
    - exact (fiber_functor_dep_to_lin_monoidal_data Γ).
    - exact (fiber_functor_dep_to_lin_monoidal_lax_laws Γ).
  Defined.

  Definition fiber_functor_dep_to_lin_monoidal
             (Γ : assembly AC)
    : fmonoidal
        (dependent_assembly_cartesian_monoidalcat _)
        (linear_assembly_sym_mon_closed_cat _)
        (fiber_functor dep_to_lin_assembly Γ).
  Proof.
    simple refine (_ ,, _).
    - exact (fiber_functor_dep_to_lin_monoidal_lax Γ).
    - split.
      + intros X₁ X₂.
        use make_is_z_isomorphism.
        * exact (fiber_functor_dep_to_lin_tensor_inv X₁ X₂).
        * abstract
            (split ;
             use lin_dep_assembly_morphism_eq ;
             intros ;
             apply fiber_comp_lin_dep_assembly).
      + use make_is_z_isomorphism.
        * exact (fiber_functor_dep_to_lin_unit_inv Γ).
        * abstract
            (split ;
             use lin_dep_assembly_morphism_eq ;
             intros ;
             apply isapropunit).
  Defined.

  Proposition fiber_functor_dep_to_lin_symmetric_monoidal
              (Γ : assembly AC)
    : is_symmetric_monoidal_functor
        (dependent_assembly_cartesian_monoidalcat_symmetric _)
        (linear_assembly_symmetric_monoidal _)
        (fiber_functor_dep_to_lin_monoidal_lax Γ).
  Proof.
    intros X Y.
    use lin_dep_assembly_morphism_eq.
    intros x y.
    refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
    apply pathsinv0.
    refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
    apply pathsdirprod ; refine (fiber_comp_dep_assembly _ _ _ @ _) ; simpl.
    - etrans.
      {
        apply maponpaths.
        unfold monoidal_cat_tensor_mor, functoronmorphisms1.
        refine (fiber_comp_dep_assembly
                  (rightwhiskering_on_morphisms
                     (dependent_assembly_cartesian_monoidalcat Γ)
                     _ _ _ _)
                  (leftwhiskering_on_morphisms _ _ _ _ _)
                  _).
      }
      refine (fiber_comp_dep_assembly _ _ _ @ _).
      cbn -[fiber_category].
      refine (fiber_comp_dep_assembly _ _ _ @ _).
      apply idpath.
    - etrans.
      {
        apply maponpaths.
        unfold monoidal_cat_tensor_mor, functoronmorphisms1.
        refine (fiber_comp_dep_assembly
                  (rightwhiskering_on_morphisms
                     (dependent_assembly_cartesian_monoidalcat Γ)
                     _ _ _ _)
                  (leftwhiskering_on_morphisms _ _ _ _ _)
                  _).
      }
      refine (fiber_comp_dep_assembly _ _ _ @ _).
      cbn -[fiber_category].
      etrans.
      {
        apply maponpaths.
        apply fiber_comp_dep_assembly.
      }
      cbn.
      apply idpath.
  Qed.      

  (** * 2.2. This functor is Cartesian *)
  Section CartesianLinAssembly.
    Context {Γ₁ Γ₂ : assembly AC}
            {s : assembly_morphism Γ₁ Γ₂}
            {X₁ : dep_assembly Γ₂}
            {Γ₃ : assembly AC}
            {s' : assembly_morphism Γ₃ Γ₁}
            {X₂ : dep_assembly Γ₃}
            (f : lin_dep_assembly_morphism
                   X₂
                   (excl_lin_assembly X₁)
                   (comp_assembly_morphism_bi s' s)).

    Definition is_cartesian_dep_to_lin_assembly_mor
      : lin_dep_assembly_morphism X₂ (excl_lin_assembly (λ x, X₁ (s x))) s'.
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x xx, f x xx).
      - abstract
          (pose proof (lin_dep_assembly_morphism_function_track f) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a & p) ;
           use hinhpr ;
           refine (a ,, _) ;
           intros x xx b₁ b₂ p₁ p₂ ;
           specialize (p x xx b₁ b₂ p₁ p₂) ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (c & q₁ & q₂) ;
           rewrite q₁ ;
           use hinhpr ;
           refine (c ,, idpath _ ,, q₂)).
    Defined.

    Proposition is_cartesian_dep_to_lin_assembly_eq
      : comp_lin_dep_assembly_morphism
          is_cartesian_dep_to_lin_assembly_mor
          (dep_to_lin_dep_assembly_morphism (dep_assembly_subst_mor _ X₁))
        =
        f.
    Proof.
      use lin_dep_assembly_morphism_eq.
      intros x xx ; cbn.
      apply idpath.
    Qed.

    Proposition is_cartesian_dep_to_lin_assembly_unique
      : isaprop
          (∑ gg,
            comp_lin_dep_assembly_morphism
              gg
              (dep_to_lin_dep_assembly_morphism (dep_assembly_subst_mor _ X₁))
            =
            f).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isaset_lin_dep_assembly_morphism.
      }
      use lin_dep_assembly_morphism_eq.
      intros x xx.
      exact (lin_dep_assembly_morphism_eq_point (pr2 φ₁ @ pathsinv0 (pr2 φ₂)) xx).
    Qed.  
  End CartesianLinAssembly.
  
  Definition is_cartesian_dep_to_lin_assembly
    : is_cartesian_disp_functor dep_to_lin_assembly.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact (dep_assembly_cleaving AC).
    }
    cbn.
    intros Γ₁ Γ₂ s X₁ Γ₃ s' X₂ f.
    cbn in *.
    use iscontraprop1.
    - exact (is_cartesian_dep_to_lin_assembly_unique f).
    - refine (is_cartesian_dep_to_lin_assembly_mor f ,, _).
      apply is_cartesian_dep_to_lin_assembly_eq.
  Defined.

  (** * 3. The unit and counit *)
  Definition dep_lin_assembly_unit
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_identity (disp_cat_of_dep_assembly AC))
        (disp_functor_composite dep_to_lin_assembly lin_to_dep_assembly).
  Proof.
    simple refine (_ ,, _).
    - intros Γ X ; cbn.
      use make_dep_assembly_morphism.
      + exact (λ x xx, xx).
      + abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x xx b₁ b₂ p₁ p₂ ;
           use hinhpr ; cbn ;
           refine (b₂ ,, _) ;
           rewrite linear_combinatory_algebra_ks_eq ;
           exact (idpath _ ,, p₂)).
    - abstract
        (intros Γ₁ Γ₂ s X₁ X₂ f ;
         use dep_assembly_morphism_eq ;
         intros x xx ;
         apply pathsinv0 ;
         etrans ; [ apply transportb_dep_assembly_mor | ] ;
         cbn ;
         apply (transportf_set X₂) ;
         apply setproperty).
  Defined.

  Definition dep_lin_assembly_counit
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_composite lin_to_dep_assembly dep_to_lin_assembly)
        (disp_functor_identity (disp_cat_of_lin_dep_assembly A)).
  Proof.
    simple refine (_ ,, _).
    - intros Γ X ; cbn.
      use make_lin_dep_assembly_morphism.
      + exact (λ x xx, xx).
      + abstract
          (use hinhpr ;
           refine ((B · (B · D) · K*)%lca ,, _) ;
           intros x xx b₁ b₂ p₁ ;
           use factor_through_squash_hProp ;
           intros (c & q₁ & q₂) ;
           rewrite q₁ ; clear q₁ ;
           cbn ;
           rewrite linear_combinatory_algebra_b_eq ;
           rewrite linear_combinatory_algebra_b_eq ;
           rewrite linear_combinatory_algebra_ks_eq ;
           rewrite linear_combinatory_algebra_d_eq ;
           exact q₂).
    - abstract
        (intros Γ₁ Γ₂ s X₁ X₂ f ;
         use lin_dep_assembly_morphism_eq ;
         intros x xx ;
         apply pathsinv0 ;
         etrans ; [ apply transportb_lin_dep_assembly_mor | ] ;
         cbn ;
         apply (transportf_set X₂) ;
         apply setproperty).
  Defined.

  (** * 4. The adjunction *)
  Definition dep_lin_assembly_adjunction_data
    : disp_adjunction_id_data
        (disp_cat_of_dep_assembly AC)
        (disp_cat_of_lin_dep_assembly A).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact dep_to_lin_assembly.
    - exact lin_to_dep_assembly.
    - exact dep_lin_assembly_unit.
    - exact dep_lin_assembly_counit.
  Defined.

  Proposition dep_lin_assembly_adjunction_laws
    : form_disp_adjunction_id dep_lin_assembly_adjunction_data.
  Proof.
    split.
    - intros Γ X.
      use lin_dep_assembly_morphism_eq.
      intros x xx.
      apply pathsinv0.
      etrans.
      {
        apply transportb_lin_dep_assembly_mor.
      }
      cbn.
      apply (transportf_set X).
      apply setproperty.
    - intros Γ X.
      use dep_assembly_morphism_eq.
      intros x xx.
      apply pathsinv0.
      etrans.
      {
        apply transportb_dep_assembly_mor.
      }
      cbn.
      apply (transportf_set X).
      apply setproperty.
  Qed.
  
  Definition dep_lin_assembly_adjunction
    : disp_adjunction_id
        (disp_cat_of_dep_assembly AC)
        (disp_cat_of_lin_dep_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact dep_lin_assembly_adjunction_data.
    - exact dep_lin_assembly_adjunction_laws.
  Defined.

  (** * 5. An isomorphism for terms *)
  Section TermIso.
    Context {Γ : assembly AC}
            (Ξ X₁ X₂ : dep_assembly Γ).

    Section Map.
      Context (f : lin_dep_assembly_morphism
                     (monoidal_product_lin_dep_assembly
                        (excl_lin_assembly X₁)
                        Ξ)
                     X₂
                     (id_assembly_morphism _)).

      Let φ
          (x : total_assembly (λ x : Γ, X₁ x))
          (xx : lin_dep_assembly_subst (total_assembly_pr X₁) Ξ x)
        : lin_dep_assembly_subst
            (total_assembly_pr X₁)
            X₂
            (id_assembly_morphism (total_assembly X₁) x)
        := f (pr1 x) (pr2 x ,, xx).

      Proposition lin_to_dep_assembly_mor_weq_map_tracker
        : lin_dep_assembly_morphism_tracker φ.
      Proof.
        pose proof (lin_dep_assembly_morphism_function_track f) as p.
        revert p.
        use factor_through_squash_hProp.
        intros (a & p).
        use hinhpr.
        refine (lca_lnl_f · a ,, _)%lca.
        intros (x & y) xx b₁ b₂ (q₁ & q₂) q₃.
        rewrite lca_lnl_f_eq.
        apply p.
        - exact q₁.
        - use hinhpr.
          refine (!(π₂%ca : AC) · b₁ ,, b₂ ,, _)%lca.
          repeat split.
          + use hinhpr ; simpl.
            refine ((π₂%ca : AC) · b₁ ,, _)%lca.
            repeat split.
            exact q₂.
          + simpl.
            exact q₃.
      Qed.
      
      Definition lin_to_dep_assembly_mor_weq_map                   
        : lin_dep_assembly_morphism
            (lin_dep_assembly_subst (total_assembly_pr X₁) Ξ)
            (lin_dep_assembly_subst (total_assembly_pr X₁) X₂)
            (id_assembly_morphism _).
      Proof.
        use make_lin_dep_assembly_morphism.
        - exact φ.
        - exact lin_to_dep_assembly_mor_weq_map_tracker.
      Defined.
    End Map.

    Section Inv.
      Context (f : lin_dep_assembly_morphism
                     (lin_dep_assembly_subst (total_assembly_pr X₁) Ξ)
                     (lin_dep_assembly_subst (total_assembly_pr X₁) X₂)
                     (id_assembly_morphism _)).

      Let φ
          (x : Γ)
          (xx : monoidal_product_lin_dep_assembly (excl_lin_assembly X₁) Ξ x)
        : X₂ x
        := f (x ,, pr1 xx) (pr2 xx).

      Proposition lin_to_dep_assembly_mor_weq_inv_tracker
        : lin_dep_assembly_morphism_tracker (s := id_assembly_morphism _) φ.
      Proof.
        pose proof (lin_dep_assembly_morphism_function_track f) as p.
        revert p.
        use factor_through_squash_hProp.
        intros (a & p).
        use hinhpr.
        refine (lca_lnl_b · a ,, _)%lca.
        intros x (y₁ & y₂) b₁ b₂ q.
        use factor_through_squash_hProp.
        intros (c₁ & c₂ & r₁ & r₂ & r₃).
        revert r₁.
        use factor_through_squash_hProp.
        intros (c₃ & r₄ & r₅).
        cbn -[lca_to_ca_app].
        rewrite r₃ ; clear r₃.
        rewrite r₄ ; clear r₄.
        rewrite lca_lnl_b_eq.
        use (p (x ,, y₁) y₂).
        - split.
          + rewrite combinatory_algebra_pr1_pair.
            exact q.
          + rewrite combinatory_algebra_pr2_pair.
            exact r₅.
        - exact r₂.
      Qed.
      
      Definition lin_to_dep_assembly_mor_weq_inv
        : lin_dep_assembly_morphism
            (monoidal_product_lin_dep_assembly
               (excl_lin_assembly X₁)
               Ξ)
            X₂
            (id_assembly_morphism _).
      Proof.
        use make_lin_dep_assembly_morphism.
        - exact φ.
        - exact lin_to_dep_assembly_mor_weq_inv_tracker.
      Defined.
    End Inv.
    
    Definition lin_to_dep_assembly_mor_weq
      : lin_dep_assembly_morphism
          (monoidal_product_lin_dep_assembly
             (excl_lin_assembly X₁)
             Ξ)
          X₂
          (id_assembly_morphism _)
        ≃
        lin_dep_assembly_morphism
          (lin_dep_assembly_subst (total_assembly_pr X₁) Ξ)
          (lin_dep_assembly_subst (total_assembly_pr X₁) X₂)
          (id_assembly_morphism _).
    Proof.
      use weq_iso.
      - exact lin_to_dep_assembly_mor_weq_map.
      - exact lin_to_dep_assembly_mor_weq_inv.
      - abstract
          (intro f ;
           use lin_dep_assembly_morphism_eq ;
           intros x xx ;
           apply idpath).
      - abstract
          (intro f ;
           use lin_dep_assembly_morphism_eq ;
           intros x xx ;
           apply idpath).
    Defined.
  End TermIso.
End LinearNonLinearAssembly.
