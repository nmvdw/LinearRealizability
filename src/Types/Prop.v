(**

 Impredicative universe of propositions for assemblies

 We establish that the linear realisability model has an impredicative universe of
 propositions. This universe classifies subsingleton assemblies (i.e., assemblies
 with at most one element). We show that the universe of propositions contains
 the following Cartesian type formers:
 - the empty type
 - the unit type
 - binary products of types
 - dependent products (and thus function types as well)
 - identity types
 We also show that it contains the following linear type formers:
 - the empty linear type (i.e., additive zero)
 - the unit linear type (i.e., additive one)
 - the monoidal unit (i.e., the multiplicative unit)
 - the monoidal product (i.e., the multiplicative conjunction)
 - binary products (i.e., additive conjunction)
 - linear function types (i.e., linear implication)
 - linear ∏-types (i.e., universal quantification)
 - multiplication and linearization, and, as a consequence, the linear exponential
 - equalizers

 The following has to be note: each subsingleton assembly is modest. Concretely,
 this means that the universe of propositions is contained in the impredicative
 universe of sets. In addition, we can show that the universe of propositions
 is not a modest set, which makes sense, because it would be inconsistent.

 Contents
 1. Subsingleton assemblies
 2. Universe of propositions
 3. Subsingleton families are in the universe
 4. Examples of subsingletons families (Cartesian type formers)
 5. Subsingleton linear assemblies are classified
 6. Examples of subsingletons (linear type formers)

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Assemblies.LinearAssemblyMonoidal.
Require Import Assemblies.ModestSet.
Require Import Types.DependentProducts.
Require Import Types.DependentSums.
Require Import Types.FiberAssembly.
Require Import Types.Terms.
Require Import Types.ImpredicativeUniverse.
Require Import Types.LinearFiber.
Require Import Types.LinearNonLinear.
Require Import Types.LinearPi.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

(** * 1. Subsingleton assemblies *)
Definition is_subsingleton_dep_assembly
           {A : combinatory_algebra}
           {Γ : assembly A}
           (X : dep_assembly Γ)
  : UU
  := ∏ (x : Γ), isaprop (X x).

Proposition subsingleton_to_modest_dep_assembly
            {A : combinatory_algebra}
            {Γ : assembly A}
            {X : dep_assembly Γ}
            (HX : is_subsingleton_dep_assembly X)
  : is_modest_dep_assembly X.
Proof.
  intros x a xx₁ xx₂ p q.
  apply HX.
Qed.

Section PropUniverse.
  Context {A : combinatory_algebra}.

  (** * 2. Universe of propositions *)
  Definition assembly_prop_universe_type
             (Γ : assembly A)
    : dep_assembly Γ
    := λ x, discrete_assembly A (funset A hPropset).

  Proposition not_modest_assembly_prop_universe_type
             (Γ : assembly A)
             (H : is_modest_dep_assembly (assembly_prop_universe_type Γ))
             (x : Γ)
    : ∅.
  Proof.
    specialize (H x I (λ _, htrue) (λ _, hfalse) tt tt).
    pose (eqtohomot H I) as p.
    cbn in p.
    exact (transportf (λ x, pr1 x) p tt).
  Qed.
  
  Definition assembly_prop_universe_el
             {Γ : assembly A}
             (t : assembly_term (assembly_prop_universe_type Γ))
    : dep_assembly Γ.
  Proof.
    intro x.
    use make_assembly.
    - exact (hProp_to_hSet (∃ (a : A), (t x a : hProp))).
    - exact (λ a _, (t x a : hProp)).
    - abstract
        (intros ? ? ;
         apply propproperty).
    - exact (λ p, p).
  Defined.

  Proposition is_subsingleton_dep_assembly_assembly_prop_universe_el
              {Γ : assembly A}
              (t : assembly_term (assembly_prop_universe_type Γ))
    : is_subsingleton_dep_assembly (assembly_prop_universe_el t).
  Proof.
    intro.
    apply propproperty.
  Qed.

  (** * 3. Subsingleton families are in the universe *)
  Section PropUniverseIso.
    Context {Γ : assembly A}
            (X : dep_assembly Γ)
            (HX : is_subsingleton_dep_assembly X).

    Definition subsingleton_to_prop
      : assembly_term (assembly_prop_universe_type Γ).
    Proof.
      use make_assembly_term.
      - exact (λ x a, ∃ (xx : X x), a ⊩ xx).
      - abstract
          (use hinhpr ;
           refine (I ,, _) ;
           intros ; cbn ;
           exact tt).
    Defined.        
    
    Definition subsingleton_to_prop_mor
      : dep_assembly_morphism
          (assembly_prop_universe_el subsingleton_to_prop)
          X
          (id_assembly_morphism Γ).
    Proof.
      use make_dep_assembly_morphism.
      - intro x.
        use factor_through_squash ; [ apply HX | ].
        intros (a & xx) ; revert xx.
        use factor_through_squash ; [ apply HX | ].
        exact (λ x, pr1 x).
      - use hinhpr.
        refine (K* ,, _).
        intros x.
        use factor_dep_through_squash.
        {
          intro.
          repeat (use impred_isaprop ; intro).
          apply propproperty.
        }
        intros (a & xx) ; revert xx.
        use factor_dep_through_squash.
        {
          intro.
          repeat (use impred_isaprop ; intro).
          apply propproperty.
        }
        intros (xx & pp) b₁ b₂ q₁ q₂ ; cbn.
        rewrite combinatory_algebra_ks_eq.
        revert q₂.
        use factor_through_squash_hProp.
        intros (yy & r).
        assert (xx = yy) as -> by apply HX.
        exact r.
    Qed.

    Definition subsingleton_to_prop_inv
      : dep_assembly_morphism
          X
          (assembly_prop_universe_el subsingleton_to_prop)
          (id_assembly_morphism Γ).
    Proof.
      use make_dep_assembly_morphism.
      - intros x xx.
        pose proof (assembly_realizes_el xx) as p.
        revert p.
        use factor_through_squash_hProp.
        intros (a & p).
        exact (hinhpr (a ,, hinhpr (xx ,, p))).
      - use hinhpr.
        refine (K* ,, _).
        intros x xx b₁ b₂ p₁ p₂.
        use hinhpr.
        cbn.
        refine (xx ,, _).
        rewrite combinatory_algebra_ks_eq.
        exact p₂.
    Qed.

    Proposition subsingleton_to_prop_iso_laws
      : is_inverse_in_precat
          (C := (disp_cat_of_dep_assembly A)[{_}])
          subsingleton_to_prop_mor
          subsingleton_to_prop_inv.
    Proof.
      split.
      - use dep_assembly_morphism_eq.
        intros x xx.
        apply propproperty.
      - use dep_assembly_morphism_eq.
        intros x xx.
        apply HX.
    Qed.
    
    Definition subsingleton_to_prop_iso
      : z_iso
          (C := (disp_cat_of_dep_assembly A)[{_}])
          (assembly_prop_universe_el subsingleton_to_prop)
          X.
    Proof.
      use make_z_iso.
      - exact subsingleton_to_prop_mor.
      - exact subsingleton_to_prop_inv.
      - exact subsingleton_to_prop_iso_laws.
    Defined.
  End PropUniverseIso.

  (** * 4. Examples of subsingletons families (Cartesian type formers) *)
  Proposition is_subsingleton_dep_prod
              {Γ₁ Γ₂ : assembly A}
              (s : assembly_morphism Γ₁ Γ₂)
              (X : dep_assembly Γ₁)
              (HX : is_subsingleton_dep_assembly X)
    : is_subsingleton_dep_assembly (dep_assembly_dep_prod s X).
  Proof.
    intros x.
    use invproofirrelevance.
    intros f₁ f₂.
    use dependent_mor_assembly_eq.
    intros xx.
    apply HX.
  Qed.

  Proposition is_subsingleton_terminal
              (Γ : assembly A)
    : is_subsingleton_dep_assembly (terminal_dep_assembly Γ).
  Proof.
    intros x.
    apply isapropunit.
  Qed.

  Proposition is_subsingleton_initial
              (Γ : assembly A)
    : is_subsingleton_dep_assembly (initial_obj_dep_assembly Γ).
  Proof.
    intros x.
    apply isapropempty.
  Qed.

  Proposition is_subsingleton_binprod
              {Γ : assembly A}
              {X₁ X₂ : dep_assembly Γ}
              (HX₁ : is_subsingleton_dep_assembly X₁)
              (HX₂ : is_subsingleton_dep_assembly X₂)
    : is_subsingleton_dep_assembly (binprod_dep_assembly Γ X₁ X₂).
  Proof.
    intros x.
    apply isapropdirprod.
    - apply HX₁.
    - apply HX₂.
  Qed.

  Proposition is_subsingleton_dep_assembly_ext_id
              {Γ : assembly A}
              (X : dep_assembly Γ)
    : is_subsingleton_dep_assembly (dep_assembly_ext_id X).
  Proof.
    intros ((x₁ & xx₁) & xx₂).
    use invproofirrelevance.
    cbn.
    intros ((x₂ & yy₁) & yy₂ & p) ((x₃ & zz₁) & zz₂ & q).
    cbn in *.
    use subtypePath.
    {
      intros x.
      use isapropdirprod.
      {
        apply isapropunit.
      }
      use isaset_total2.
      - use isaset_total2.
        + apply setproperty.
        + intro.
          apply setproperty.
      - intro.
        apply setproperty.
    }
    exact (maponpaths pr1 (p @ !q)).
  Qed.
End PropUniverse.

Local Open Scope lca.

Section LinearProp.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  Section UniverseIso.
    Context {Γ : assembly AC}
            (X : dep_assembly Γ)
            (HX : is_subsingleton_dep_assembly X).

    (** * 5. Subsingleton linear assemblies are classified *)
    Definition linear_subsingleton_to_prop_mor
      : lin_dep_assembly_morphism
          (assembly_prop_universe_el (subsingleton_to_prop X))
          X
          (id_assembly_morphism Γ).
    Proof.
      use make_lin_dep_assembly_morphism.
      - intro x.
        use factor_through_squash ; [ apply HX | ].
        intros (a & xx) ; revert xx.
        use factor_through_squash ; [ apply HX | ].
        exact (λ x, pr1 x).
      - use hinhpr.
        refine (K* ,, _).
        intros x.
        use factor_dep_through_squash.
        {
          intro.
          repeat (use impred_isaprop ; intro).
          apply propproperty.
        }
        intros (a & xx) ; revert xx.
        use factor_dep_through_squash.
        {
          intro.
          repeat (use impred_isaprop ; intro).
          apply propproperty.
        }
        intros (xx & pp) b₁ b₂ q₁ q₂ ; cbn.
        rewrite linear_combinatory_algebra_ks_eq.
        revert q₂.
        use factor_through_squash_hProp.
        intros (yy & r).
        assert (xx = yy) as -> by apply HX.
        exact r.
    Qed.

    Definition linear_subsingleton_to_prop_inv
      : lin_dep_assembly_morphism
          X
          (assembly_prop_universe_el (subsingleton_to_prop X))
          (id_assembly_morphism Γ).
    Proof.
      use make_lin_dep_assembly_morphism.
      - intros x xx.
        pose proof (assembly_realizes_el xx) as p.
        revert p.
        use factor_through_squash_hProp.
        intros (a & p).
        exact (hinhpr (a ,, hinhpr (xx ,, p))).
      - use hinhpr.
        refine (K* ,, _).
        intros x xx b₁ b₂ p₁ p₂.
        use hinhpr.
        cbn.
        refine (xx ,, _).
        rewrite linear_combinatory_algebra_ks_eq.
        exact p₂.
    Qed.

    Proposition linear_subsingleton_to_prop_iso_laws
      : is_inverse_in_precat
          (C := (disp_cat_of_lin_dep_assembly A)[{_}])
          linear_subsingleton_to_prop_mor
          linear_subsingleton_to_prop_inv.
    Proof.
      split.
      - use lin_dep_assembly_morphism_eq.
        intros x xx.
        apply propproperty.
      - use lin_dep_assembly_morphism_eq.
        intros x xx.
        apply HX.
    Qed.
    
    Definition linear_subsingleton_to_prop_iso
      : z_iso
          (C := (disp_cat_of_lin_dep_assembly A)[{_}])
          (assembly_prop_universe_el (subsingleton_to_prop X))
          X.
    Proof.
      use make_z_iso.
      - exact linear_subsingleton_to_prop_mor.
      - exact linear_subsingleton_to_prop_inv.
      - exact linear_subsingleton_to_prop_iso_laws.
    Defined.
  End UniverseIso.

  (** * 6. Examples of subsingletons (linear type formers) *)
  Proposition is_subsingleton_lin_unit_dep_assembly
              (Γ : assembly AC)
    : is_subsingleton_dep_assembly (unit_dep_assembly Γ).
  Proof.
    intros x.
    use invproofirrelevance.
    intros f₁ f₂.
    apply isapropunit.
  Qed.

  Proposition is_subsingleton_monoidal_product_lin_dep_assembly
              {Γ : assembly AC}
              {X₁ X₂ : dep_assembly Γ}
              (HX₁ : is_subsingleton_dep_assembly X₁)
              (HX₂ : is_subsingleton_dep_assembly X₂)
    : is_subsingleton_dep_assembly (monoidal_product_lin_dep_assembly X₁ X₂).
  Proof.
    intros x.
    apply isapropdirprod.
    - apply HX₁.
    - apply HX₂.
  Qed.

  Proposition is_subsingleton_linear_initial
              (Γ : assembly A)
    : is_subsingleton_dep_assembly (initial_obj_linear_assembly Γ).
  Proof.
    intros x.
    apply isapropempty.
  Qed.

  Proposition is_subsingleton_binprod_linear_assembly
              {Γ : assembly AC}
              {X₁ X₂ : dep_assembly Γ}
              (HX₁ : is_subsingleton_dep_assembly X₁)
              (HX₂ : is_subsingleton_dep_assembly X₂)
    : is_subsingleton_dep_assembly (binprod_linear_assembly Γ X₁ X₂).
  Proof.
    intros x.
    apply isapropdirprod.
    - apply HX₁.
    - apply HX₂.
  Qed.

  Proposition is_subsingleton_linear_assembly_functions
              {Γ : assembly AC}
              {X₁ X₂ : dep_assembly Γ}
              (HX₂ : is_subsingleton_dep_assembly X₂)
    : is_subsingleton_dep_assembly (linear_assembly_functions Γ X₁ X₂).
  Proof.
    intros x.
    use invproofirrelevance.
    intros f₁ f₂.
    use linear_assembly_fiber_function_eq.
    intros.
    apply HX₂.
  Qed.

  Proposition is_subsingleton_linear_pi_dep_assembly
              {Γ₁ Γ₂ : assembly AC}
              (s : assembly_morphism Γ₁ Γ₂)
              (X : dep_assembly Γ₁)
              (HX : is_subsingleton_dep_assembly X)
    : is_subsingleton_dep_assembly (linear_pi_dep_assembly s X).
  Proof.
    intros x.
    use invproofirrelevance.
    intros f₁ f₂.
    use lin_dependent_mor_eq.
    intros.
    apply HX.
  Qed.

  Proposition is_subsingleton_excl_lin_assembly
              {Γ : assembly AC}
              (X : dep_assembly Γ)
              (HX : is_subsingleton_dep_assembly X)
    : is_subsingleton_dep_assembly (excl_lin_assembly X).
  Proof.
    apply HX.
  Qed.

  Proposition is_subsingleton_equalizer_linear_assembly
              {Γ : assembly AC}
              {X₁ X₂ : dep_assembly Γ}
              (HX₁ : is_subsingleton_dep_assembly X₁)
              (f g : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism Γ))
    : is_subsingleton_dep_assembly (equalizer_linear_assembly Γ f g).
  Proof.
    intro x.
    use invproofirrelevance.
    intros xx₁ xx₂.
    use subtypePath.
    {
      intro.
      apply setproperty.
    }
    apply HX₁.
  Qed.
End LinearProp.
