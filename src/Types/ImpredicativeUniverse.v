(**

 Impredicative universe for assemblies

 Contents
 1. Universe of assemblies
 2. Modest families
 3. Modest families are in the universe
 4. Dependent products of modest families
 5. Modest families in the linear case
 6. All modest sets are in the universe

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.

Require Import SetFamilies.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.Combinators.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Assemblies.LinearAssemblyMonoidal.
Require Import Assemblies.ModestSet.
Require Import Assemblies.PartialEqRel.
Require Import Assemblies.ModestSetEquiv.
Require Import Types.DependentProducts.
Require Import Types.LinearPi.
Require Import Types.LinearFiber.
Require Import Types.LinearNonLinear.
Require Import Types.Terms.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

Section UniverseType.
  Context {A : combinatory_algebra}.

  (** * 1. Universe of assemblies *)
  Definition assembly_universe_type
             (Γ : assembly A)
    : dep_assembly Γ
    := λ x, discrete_assembly A (ca_per_hSet A).

  Definition assembly_universe_el
             {Γ : assembly A}
             (t : assembly_term (assembly_universe_type Γ))
    : dep_assembly Γ
    := λ x, per_to_assembly (t x).

  (** * 2. Modest families *)
  Definition is_modest_dep_assembly
             {Γ : assembly A}
             (X : dep_assembly Γ)
    : hProp
    := ∀ (x : Γ), is_modest (X x).

  Definition modest_dep_assembly_modest_set
             {Γ : assembly A}
             (X : dep_assembly Γ)
             (HX : is_modest_dep_assembly X)
             (x : Γ)
    : modest_set A.
  Proof.
    use make_modest_set.
    - exact (X x).
    - exact (HX x).
  Defined.
    
  Definition is_modest_dep_assembly_ca_per
             {Γ : assembly A}
             (X : dep_assembly Γ)
             (HX : is_modest_dep_assembly X)
    : assembly_term (assembly_universe_type Γ).
  Proof.
    use make_assembly_term.
    - exact (λ x, modest_set_to_per (modest_dep_assembly_modest_set X HX x)).
    - abstract
        (use hinhpr ;
         refine (I ,, _)%ca ;
         intros ;
         apply tt).
  Defined.

  (** * 3. Modest families are in the universe *)
  Section UniverseIso.
    Context {Γ : assembly A}
            (X : dep_assembly Γ)
            (HX : is_modest_dep_assembly X).

    Definition is_modest_dep_assembly_ca_per_mor
      : dep_assembly_morphism
          (assembly_universe_el (is_modest_dep_assembly_ca_per X HX))
          X
          (id_assembly_morphism Γ).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x, modest_set_to_per_z_iso_mor
                      (modest_dep_assembly_modest_set X HX x)).
      - abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x ;
           use setquotunivprop' ;
           [ intro ; repeat (use impred ; intro) ; apply propproperty | ] ;
           intros ( a & xx & p₁ & p₂ ) b₁ b₂ q₁ ( xx' & q₂ & q₃ ) ; cbn ;
           cbn in q₃ ;
           rewrite combinatory_algebra_ks_eq ;
           rewrite (is_modest_modest_set _ p₁ q₃) ;
           exact q₂).
    Defined.

    Definition is_modest_dep_assembly_ca_per_inv
      : dep_assembly_morphism
          X
          (assembly_universe_el (is_modest_dep_assembly_ca_per X HX))
          (id_assembly_morphism Γ).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x, modest_set_to_per_z_iso_inv
                      (modest_dep_assembly_modest_set X HX x)).
      - abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x xx b₁ b₂ p₁ p₂ ;
           rewrite combinatory_algebra_ks_eq ;
           pose proof (assembly_realizes_el x) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros (b & q) ;
           simpl ;
           pose (unique_fiber_modest_set_to_per
                   (X := modest_dep_assembly_modest_set X HX x)
                   xx)
             as z₁ ;
           pose (unique_fiber_modest_set_to_per_el
                   (X := modest_dep_assembly_modest_set X HX x)
                   xx
                   p₂)
             as z₂ ;
           assert (pr11 z₁ = pr1 z₂) as r ;
           [ apply (maponpaths
                      pr1
                      (proofirrelevance _ (isaprop_fiber_modest_set_to_per _) _ _))
           | ] ;
           unfold z₁ in r ;
           rewrite r ;
           cbn ;
           exact (xx ,, p₂ ,, p₂)).
    Defined.

    Proposition is_modest_dep_assembly_ca_per_z_iso_laws
      : is_inverse_in_precat
          (C := (disp_cat_of_dep_assembly A)[{_}])
          is_modest_dep_assembly_ca_per_mor
          is_modest_dep_assembly_ca_per_inv.
    Proof.
      split.
      - use dep_assembly_morphism_eq.
        intros x xx.
        etrans.
        {
          apply fiber_comp_dep_assembly.
        }
        exact (eq_modest_set_morphism_point
                 (pr1 (modest_set_to_per_z_iso_laws
                         (modest_dep_assembly_modest_set X HX x)))
                 xx).
      - use dep_assembly_morphism_eq.
        intros x xx.
        etrans.
        {
          apply fiber_comp_dep_assembly.
        }
        exact (eq_modest_set_morphism_point
                 (pr2 (modest_set_to_per_z_iso_laws
                         (modest_dep_assembly_modest_set X HX x)))
                 xx).
    Qed.
    
    Definition is_modest_dep_assembly_ca_per_z_iso
      : z_iso
          (C := (disp_cat_of_dep_assembly A)[{_}])
          (assembly_universe_el
             (is_modest_dep_assembly_ca_per X HX))
          X.
    Proof.
      use make_z_iso.
      - exact is_modest_dep_assembly_ca_per_mor.
      - exact is_modest_dep_assembly_ca_per_inv.
      - exact is_modest_dep_assembly_ca_per_z_iso_laws.
    Defined.
  End UniverseIso.

  (** * 4. Dependent products of modest families *)
  Definition is_modest_family_dep_prod
             {Γ₁ Γ₂ : assembly A}
             (s : assembly_morphism Γ₁ Γ₂)
             (X : dep_assembly Γ₁)
             (HX : is_modest_dep_assembly X)
    : is_modest_dep_assembly (dep_assembly_dep_prod s X).
  Proof.
    intros y a f₁ f₂ p₁ p₂.
    use dependent_mor_assembly_eq.
    intros ( x & q ).
    pose proof (assembly_realizes_el x) as r.
    revert r.
    use factor_through_squash.
    {
      apply setproperty.
    }
    intros ( b & r ).
    use HX.
    + exact (a · b)%ca.
    + use p₁.
      exact r.
    + use p₂.
      exact r.
  Qed.
End UniverseType.

Local Open Scope lca.

Section Linear.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  (** * 5. Modest families in the linear case *)
  Definition is_modest_family_linear_dep_prod
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
             (X : dep_assembly Γ₁)
             (HX : is_modest_dep_assembly X)
    : is_modest_dep_assembly (linear_pi_dep_assembly s X).
  Proof.
    intros y a f₁ f₂ p₁ p₂.
    use dependent_mor_assembly_eq.
    intros ( x & q ).
    pose proof (assembly_realizes_el x) as r.
    revert r.
    use factor_through_squash.
    {
      apply setproperty.
    }
    intros ( b & r ).
    use HX.
    + exact (a · b)%ca.
    + use p₁.
      exact r.
    + use p₂.
      exact r.
  Qed.

  Definition is_modest_family_linear_assembly_functions
             {Γ : assembly AC}
             (X₁ X₂ : dep_assembly Γ)
             (HX : is_modest_dep_assembly X₂)
    : is_modest_dep_assembly (linear_assembly_functions _ X₁ X₂).
  Proof.
    intros y a f g p₁ p₂.
    use linear_assembly_fiber_function_eq.
    intros x.
    pose proof (assembly_realizes_el x) as r.
    revert r.
    use factor_through_squash.
    {
      apply setproperty.
    }
    intros ( b & r ).    
    use HX.
    - exact ((a : A) · b).
    - use p₁.
      exact r.
    - use p₂.
      exact r.
  Qed.

  Definition is_modest_family_initial_obj_linear_assembly
             (Γ : assembly AC)
    : is_modest_dep_assembly (initial_obj_linear_assembly Γ).
  Proof.
    intros y a x.
    induction x.
  Qed.

  Definition is_modest_family_terminal_obj_linear_assembly
             (Γ : assembly AC)
    : is_modest_dep_assembly (terminal_dep_assembly Γ).
  Proof.
    repeat intro.
    apply isapropunit.
  Qed.

  Definition is_modest_family_unit_dep_assembly
             (Γ : assembly AC)
    : is_modest_dep_assembly (unit_dep_assembly Γ).
  Proof.
    repeat intro.
    apply isapropunit.
  Qed.
  
  Definition is_modest_family_equalizer_dep_assembly
             {Γ : assembly AC}
             {X₁ X₂ : dep_assembly Γ}
             (f g : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism _))
             (HX : is_modest_dep_assembly X₁)
    : is_modest_dep_assembly (equalizer_linear_assembly _ f g).
  Proof.
    intros x a y₁ y₂ p₁ p₂.
    use subtypePath.
    {
      intro.
      apply setproperty.
    }
    use (HX x a).
    - exact p₁.
    - exact p₂.
  Qed.

  Definition is_modest_dep_assembly_excl_lin_assembly
             {Γ : assembly AC}
             (X : dep_assembly Γ)
             (HX : is_modest_dep_assembly X)
    : is_modest_dep_assembly (excl_lin_assembly X).
  Proof.
    intros x a y₁ y₂.
    use factor_through_squash_hProp.
    intros (b₁ & p₁ & q₁).
    use factor_through_squash_hProp.
    intros (b₂ & p₂ & q₂).
    use (HX x).
    - exact (D · a).
    - rewrite p₁.
      rewrite linear_combinatory_algebra_d_eq.
      exact q₁.
    - rewrite p₂.
      rewrite linear_combinatory_algebra_d_eq.
      exact q₂.
  Qed.

  (** * 6. All modest sets are in the universe *)
  Section UniverseIso.
    Context {Γ : assembly AC}
            (X : dep_assembly Γ)
            (HX : is_modest_dep_assembly X).

    Definition is_modest_lin_dep_assembly_ca_per_mor
      : lin_dep_assembly_morphism
          (assembly_universe_el (is_modest_dep_assembly_ca_per X HX))
          X
          (id_assembly_morphism Γ).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x, modest_set_to_per_z_iso_mor
                      (modest_dep_assembly_modest_set X HX x)).
      - abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x ;
           use setquotunivprop' ;
           [ intro ; repeat (use impred ; intro) ; apply propproperty | ] ;
           intros ( a & xx & p₁ & p₂ ) b₁ b₂ q₁ ( xx' & q₂ & q₃ ) ; cbn ;
           cbn in q₃ ;
           rewrite linear_combinatory_algebra_ks_eq ;
           rewrite (is_modest_modest_set _ p₁ q₃) ;
           exact q₂).
    Defined.

    Definition is_modest_lin_dep_assembly_ca_per_inv
      : lin_dep_assembly_morphism
          X
          (assembly_universe_el (is_modest_dep_assembly_ca_per X HX))
          (id_assembly_morphism Γ).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x, modest_set_to_per_z_iso_inv
                      (modest_dep_assembly_modest_set X HX x)).
      - abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x xx b₁ b₂ p₁ p₂ ;
           rewrite linear_combinatory_algebra_ks_eq ;
           pose proof (assembly_realizes_el x) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros (b & q) ;
           simpl ;
           pose (unique_fiber_modest_set_to_per
                   (X := modest_dep_assembly_modest_set X HX x)
                   xx)
             as z₁ ;
           pose (unique_fiber_modest_set_to_per_el
                   (X := modest_dep_assembly_modest_set X HX x)
                   xx
                   p₂)
             as z₂ ;
           assert (pr11 z₁ = pr1 z₂) as r ;
           [ apply (maponpaths
                      pr1
                      (proofirrelevance _ (isaprop_fiber_modest_set_to_per _) _ _))
           | ] ;
           unfold z₁ in r ;
           rewrite r ;
           cbn ;
           exact (xx ,, p₂ ,, p₂)).
    Defined.

    Proposition is_modest_lin_dep_assembly_ca_per_z_iso_laws
      : is_inverse_in_precat
          (C := (disp_cat_of_lin_dep_assembly A)[{_}])
          is_modest_lin_dep_assembly_ca_per_mor
          is_modest_lin_dep_assembly_ca_per_inv.
    Proof.
      split.
      - use lin_dep_assembly_morphism_eq.
        intros x xx.
        etrans.
        {
          apply fiber_comp_lin_dep_assembly.
        }
        exact (eq_modest_set_morphism_point
                 (pr1 (modest_set_to_per_z_iso_laws
                         (modest_dep_assembly_modest_set X HX x)))
                 xx).
      - use lin_dep_assembly_morphism_eq.
        intros x xx.
        etrans.
        {
          apply fiber_comp_lin_dep_assembly.
        }
        exact (eq_modest_set_morphism_point
                 (pr2 (modest_set_to_per_z_iso_laws
                         (modest_dep_assembly_modest_set X HX x)))
                 xx).
    Qed.
    
    Definition is_modest_lin_dep_assembly_ca_per_z_iso
      : z_iso
          (C := (disp_cat_of_lin_dep_assembly A)[{_}])
          (assembly_universe_el
             (is_modest_dep_assembly_ca_per X HX))
          X.
    Proof.
      use make_z_iso.
      - exact is_modest_lin_dep_assembly_ca_per_mor.
      - exact is_modest_lin_dep_assembly_ca_per_inv.
      - exact is_modest_lin_dep_assembly_ca_per_z_iso_laws.
    Defined.
  End UniverseIso.
End Linear.
