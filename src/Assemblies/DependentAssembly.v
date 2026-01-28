(**

 The comprehension category of dependent assemblies

 In this file, we define dependent assemblies and we show that they give rise to a
 comprehension category. We verify that this comprehension category is full and that
 it has a fiberwise terminal object.

 Contents
 1. Dependent assemblies and their morphisms
 2. Identity and composition of dependent assembly morphisms
 3. The displayed category of dependent assemblies
 4. The cleaving for dependent assemblies
 5. The comprehension functor
 5.1. The total assembly
 5.2. The total assembly morphism
 5.3. Comprehension of dependent assemblies
 6. The comprehension functor is fully faithful
 7. Comprehension preserves Cartesian morphism
 8. The comprehension category of assemblies
 9. The fiberwise terminal object

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

(** * 1. Dependent assemblies and their morphisms *)
Definition dep_assembly
           {A : applicative_structure}
           (Γ : assembly A)
  : UU
  := Γ → assembly A.

Proposition dep_assembly_transportf_realizes
            {A : applicative_structure}
            {Γ : assembly A}
            {X : dep_assembly Γ}
            {a : A}
            {x x' : Γ}
            (p : x = x')
            {xx : X x}
            (q : a ⊩ xx)
  : a ⊩ transportf X p xx.
Proof.
  induction p.
  exact q.
Qed.

Section DependentAssembly.
  Context {A : combinatory_algebra}.

  Definition dep_assembly_morphism_tracker
             {Γ₁ Γ₂ : assembly A}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : ∏ (x : Γ₁), X₁ x → X₂ (s x))
    : hProp
    := ∃ (a : A),
       ∏ (x : Γ₁)
         (xx : X₁ x)
         (b₁ b₂ : A),
       b₁ ⊩ x
       →
       b₂ ⊩ xx
       →
       (a · b₁ · b₂)%ca ⊩ f x xx.

  Definition dep_assembly_morphism
             {Γ₁ Γ₂ : assembly A}
             (X₁ : dep_assembly Γ₁)
             (X₂ : dep_assembly Γ₂)
             (s : assembly_morphism Γ₁ Γ₂)
    : UU
    := ∑ (f : ∏ (x : Γ₁), X₁ x → X₂ (s x)),
       dep_assembly_morphism_tracker f.

  Proposition isaset_dep_assembly_morphism
              {Γ₁ Γ₂ : assembly A}
              (X₁ : dep_assembly Γ₁)
              (X₂ : dep_assembly Γ₂)
              (s : assembly_morphism Γ₁ Γ₂)
    : isaset (dep_assembly_morphism X₁ X₂ s).
  Proof.
    use isaset_total2.
    - do 2 (use impred_isaset ; intro).
      apply setproperty.
    - intros.
      apply isasetaprop.
      apply propproperty.
  Qed.
  
  Definition make_dep_assembly_morphism
             {Γ₁ Γ₂ : assembly A}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : ∏ (x : Γ₁), X₁ x → X₂ (s x))
             (Hf : dep_assembly_morphism_tracker f)
    : dep_assembly_morphism X₁ X₂ s
    := f ,, Hf.

  Definition dep_assembly_morphism_function
             {Γ₁ Γ₂ : assembly A}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : dep_assembly_morphism X₁ X₂ s)
             (x : Γ₁)
             (xx : X₁ x)
    : X₂ (s x)
    := pr1 f x xx.

  Coercion dep_assembly_morphism_function : dep_assembly_morphism >-> Funclass.

  Proposition dep_assembly_morphism_function_track
              {Γ₁ Γ₂ : assembly A}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              (f : dep_assembly_morphism X₁ X₂ s)
    : dep_assembly_morphism_tracker f.
  Proof.
    exact (pr2 f).
  Defined.

  Proposition dep_assembly_morphism_eq
              {Γ₁ Γ₂ : assembly A}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              {f g : dep_assembly_morphism X₁ X₂ s}
              (p : ∏ (x : Γ₁) (xx : X₁ x), f x xx = g x xx)
    : f = g.
  Proof.
    use subtypePath_prop.
    use funextsec ; intro x.
    use funextsec ; intro xx.
    exact (p x xx).
  Qed.

  Proposition dep_assembly_morphism_eq_point
              {Γ₁ Γ₂ : assembly A}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              {f g : dep_assembly_morphism X₁ X₂ s}
              (p : f = g)
              {x : Γ₁}
              (xx : X₁ x)
    : f x xx = g x xx.
  Proof.
    induction p.
    apply idpath.
  Qed.

  (** * 2. Identity and composition of dependent assembly morphisms *)
  Definition id_dep_assembly_morphism
             {Γ : assembly A}
             (X : dep_assembly Γ)
    : dep_assembly_morphism X X (id_assembly_morphism Γ).
  Proof.
    use make_dep_assembly_morphism.
    - exact (λ x xx, xx).
    - abstract
        (use hinhpr ;
         refine (K* ,, _) ;
         intros x xx b₁ b₂ p₁ p₂ ;
         rewrite combinatory_algebra_ks_eq ;
         exact p₂).
  Defined.

  Definition comp_dep_assembly_morphism
             {Γ₁ Γ₂ Γ₃ : assembly A}
             {s₁ : assembly_morphism Γ₁ Γ₂}
             {s₂ : assembly_morphism Γ₂ Γ₃}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {X₃ : dep_assembly Γ₃}
             (f : dep_assembly_morphism X₁ X₂ s₁)
             (g : dep_assembly_morphism X₂ X₃ s₂)
    : dep_assembly_morphism X₁ X₃ (comp_assembly_morphism s₁ s₂).
  Proof.
    use make_dep_assembly_morphism.
    - exact (λ x xx, g _ (f x xx)).
    - abstract
        (pose proof (dep_assembly_morphism_function_track f) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros ( a_f & p_f ) ;
         pose proof (dep_assembly_morphism_function_track g) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros ( a_g & p_g ) ;
         pose proof (assembly_morphism_tracked s₁) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros ( a_s & p_s ) ;
         use hinhpr ;
         refine (Bd · a_g · a_f · a_s ,, _)%ca ;
         intros x xx b₁ b₂ q₁ q₂ ;
         rewrite combinatory_algebra_d_comp_eq ;
         specialize (p_s b₁ x q₁) ;
         use (p_g _ _ _ _ p_s) ;
         exact (p_f _ _ _ _ q₁ q₂)).
  Defined.

  (** * 3. The displayed category of dependent assemblies *)
  Definition disp_cat_of_dep_assembly_ob_mor
    : disp_cat_ob_mor (cat_of_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact dep_assembly.
    - exact (λ Γ₁ Γ₂ X₁ X₂ s, dep_assembly_morphism X₁ X₂ s).
  Defined.

  Definition disp_cat_of_dep_assembly_id_comp
    : disp_cat_id_comp
        (cat_of_assembly A)
        disp_cat_of_dep_assembly_ob_mor.
  Proof.
    split.
    - intros Γ X.
      exact (id_dep_assembly_morphism X).
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ X₁ X₂ X₃ f g.
      exact (comp_dep_assembly_morphism f g).
  Defined.      
      
  Definition disp_cat_of_dep_assembly_data
    : disp_cat_data (cat_of_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_dep_assembly_ob_mor.
    - exact disp_cat_of_dep_assembly_id_comp.
  Defined.

  Proposition transportf_dep_assembly_mor
              {Γ₁ Γ₂ : cat_of_assembly A}
              {s s' : Γ₁ --> Γ₂}
              (p : s' = s)
              {X₁ : disp_cat_of_dep_assembly_data Γ₁}
              {X₂ : pr1 disp_cat_of_dep_assembly_data Γ₂}
              (f : X₁ -->[ s' ] X₂)
              {x : pr1 Γ₁}
              (xx : X₁ x)
    : pr1 (transportf (λ z, _ -->[ z ] _) p f) x xx
      =
      transportf X₂ (assembly_morphism_eq_point p x) (pr1 f x xx).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_dep_assembly_mor
              {Γ₁ Γ₂ : cat_of_assembly A}
              {s s' : Γ₁ --> Γ₂}
              (p : s = s')
              {X₁ : disp_cat_of_dep_assembly_data Γ₁}
              {X₂ : pr1 disp_cat_of_dep_assembly_data Γ₂}
              (f : X₁ -->[ s' ] X₂)
              {x : pr1 Γ₁}
              (xx : X₁ x)
    : pr1 (transportb (λ z, _ -->[ z ] _) p f) x xx
      =
      transportb X₂ (assembly_morphism_eq_point p x) (pr1 f x xx).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition disp_cat_of_dep_assembly_axioms
    : disp_cat_axioms
        (cat_of_assembly A)
        disp_cat_of_dep_assembly_data.
  Proof.
    repeat split.
    - intros.
      use dep_assembly_morphism_eq.
      intros.
      refine (!_ @ !(transportb_dep_assembly_mor _ _ _)).
      unfold transportb.
      rewrite transportf_set.
      {
        apply idpath.
      }
      apply setproperty.
    - intros.
      use dep_assembly_morphism_eq.
      intros.
      refine (!_ @ !(transportb_dep_assembly_mor _ _ _)).
      unfold transportb.
      rewrite transportf_set.
      {
        apply idpath.
      }
      apply setproperty.
    - intros.
      use dep_assembly_morphism_eq.
      intros.
      refine (!_ @ !(transportb_dep_assembly_mor _ _ _)).
      unfold transportb.
      rewrite transportf_set.
      {
        apply idpath.
      }
      apply setproperty.
    - intros.
      apply isaset_dep_assembly_morphism.
  Qed.
  
  Definition disp_cat_of_dep_assembly
    : disp_cat (cat_of_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_dep_assembly_data.
    - exact disp_cat_of_dep_assembly_axioms.
  Defined.

  Proposition fiber_comp_dep_assembly
              {Γ : assembly A}
              {X₁ X₂ X₃ : dep_assembly Γ}
              (f : disp_cat_of_dep_assembly[{Γ}] ⟦ X₁ , X₂ ⟧)
              (g : disp_cat_of_dep_assembly[{Γ}] ⟦ X₂ , X₃ ⟧)
              {x : Γ}
              (xx : X₁ x)
    : pr1 (f · g) x xx = pr1 g _ (pr1 f _ xx).
  Proof.
    cbn.
    etrans.
    {
      exact (transportf_dep_assembly_mor (id_right _) (comp_dep_assembly_morphism f g) xx).
    }
    rewrite transportf_set.
    {
      apply idpath.
    }
    apply setproperty.
  Qed.

  Proposition idtoiso_fiber_dep_assembly
              {Γ : assembly A}
              {X₁ X₂ : dep_assembly Γ}
              (p : X₁ = X₂)
              {x : Γ}
              (xx : X₁ x)
    : pr11 (idtoiso (C := disp_cat_of_dep_assembly[{Γ}]) p) x xx
      =
      cast (maponpaths (λ z, pr11 z) (eqtohomot p x)) xx.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.
  
  (** * 4. The cleaving for dependent assemblies *)
  Section CartesianLift.
    Context {Γ₁ Γ₂ : assembly A}
            (s : assembly_morphism Γ₁ Γ₂)
            (X : dep_assembly Γ₂).

    Definition dep_assembly_subst
      : disp_cat_of_dep_assembly Γ₁
      := λ x, X(s x).

    Proposition transportf_dep_assembly_subst
                {x₁ x₂ : Γ₁}
                (p : x₁ = x₂)
                (xx : X (s x₁))
      : transportf dep_assembly_subst p xx
        =
        transportf X (maponpaths s p) xx.
    Proof.
      induction p.
      apply idpath.
    Qed.

    Definition dep_assembly_subst_mor
      : dep_assembly_morphism dep_assembly_subst X s.
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ x xx, xx).
      - abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x xx b₁ b₂ p₁ p₂ ;
           rewrite combinatory_algebra_ks_eq ;
           exact p₂).
    Defined.

    Section Cartesian.
      Context {Δ : assembly A}
              {s' : assembly_morphism Δ Γ₁}
              {X' : dep_assembly Δ}
              (f : dep_assembly_morphism X' X (comp_assembly_morphism s' s)).

      Definition dep_assembly_cartesian_factorisation
        : dep_assembly_morphism X' dep_assembly_subst s'.
      Proof.
        use make_dep_assembly_morphism.
        - exact (λ x xx, f x xx).
        - exact (dep_assembly_morphism_function_track f).
      Defined.

      Proposition dep_assembly_cartesian_factorisation_comm
        : comp_dep_assembly_morphism
            dep_assembly_cartesian_factorisation
            dep_assembly_subst_mor
          =
          f.
      Proof.
        use dep_assembly_morphism_eq.
        intros x xx ; cbn.
        apply idpath.
      Qed.

      Proposition dep_assembly_cartesian_factorisation_unique
        : isaprop
            (∑ g, comp_dep_assembly_morphism g dep_assembly_subst_mor = f).
      Proof.
        use invproofirrelevance.
        intros g₁ g₂.
        use subtypePath.
        {
          intro.
          apply isaset_dep_assembly_morphism.
        }
        use dep_assembly_morphism_eq.
        intros x xx ; cbn.
        exact (dep_assembly_morphism_eq_point (pr2 g₁ @ !(pr2 g₂)) xx).
      Qed.
    End Cartesian.    

    Definition is_cartesian_dep_assembly_subst_mor
      : is_cartesian
          (D := disp_cat_of_dep_assembly)
          dep_assembly_subst_mor.
    Proof.
      intros Δ s' X' f.
      use iscontraprop1.
      - apply dep_assembly_cartesian_factorisation_unique.
      - refine (dep_assembly_cartesian_factorisation f ,, _).
        apply dep_assembly_cartesian_factorisation_comm.
    Defined.
  End CartesianLift.

  Arguments dep_assembly_subst /.
  
  Definition dep_assembly_cleaving
    : cleaving disp_cat_of_dep_assembly.
  Proof.
    intros Γ₂ Γ₁ s X.
    simple refine (_ ,, _ ,, _).
    - exact (dep_assembly_subst s X).
    - exact (dep_assembly_subst_mor s X).
    - exact (is_cartesian_dep_assembly_subst_mor s X).
  Defined.

  Proposition fiber_functor_from_cleaving_dep_assembly
              {Γ₁ Γ₂ : assembly A}
              (s : assembly_morphism Γ₁ Γ₂)
              {X₁ X₂ : dep_assembly Γ₂}
              (f : dep_assembly_morphism X₁ X₂ (id_assembly_morphism Γ₂))
              {x : Γ₁}
              (xx : X₁(s x))
    : pr1 (#(fiber_functor_from_cleaving _ dep_assembly_cleaving s) f) x xx
      =
      f (s x) xx.
  Proof.
    cbn.
    etrans.
    {
      exact (transportf_dep_assembly_mor (id_right _ @ !(id_left _)) _ xx).
    }
    rewrite transportf_set.
    {
      apply idpath.
    }
    apply setproperty.
  Qed.

  Proposition eq_function_idtoiso_dep_assembly
              {Γ₁ Γ₂ : assembly A}
              (X : dep_assembly Γ₂)
              {s₁ s₂ : assembly_morphism Γ₁ Γ₂}
              (p : s₁ = s₂)
              {x : Γ₁}
              (xx : X (s₁ x))
    : pr11 (idtoiso
              (C := disp_cat_of_dep_assembly[{Γ₁}])
              (maponpaths (λ (f : assembly_morphism Γ₁ Γ₂) (z : Γ₁), X (f z)) p))
        x
        xx
      =
      transportf X (assembly_morphism_eq_point p x) xx.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition comm_nat_z_iso_dep_assembly
              {Γ₁ Γ₂ Γ₃ Γ₄ : assembly A}
              {f : assembly_morphism Γ₂ Γ₁}
              {g : assembly_morphism Γ₃ Γ₁}
              {h : assembly_morphism Γ₄ Γ₃}
              {k : assembly_morphism Γ₄ Γ₂}
              (p : comp_assembly_morphism k f = comp_assembly_morphism h g)
              {X : dep_assembly Γ₁}
              {x : Γ₄}
              (xx : X(f(k x)))
    : pr1 (comm_nat_z_iso dep_assembly_cleaving _ _ _ _ p X) x xx
      =
      transportf X (assembly_morphism_eq_point p x) xx.
  Proof.
    cbn.
    etrans.
    {
      use transportf_dep_assembly_mor.
    }
    simpl.
    etrans.
    {
      apply maponpaths.
      use transportf_dep_assembly_mor.
    }
    simpl.
    etrans.
    {
      do 2 apply maponpaths.
      use transportf_dep_assembly_mor.
    }
    unfold transportb ; simpl.
    etrans.
    {
      do 4 apply maponpaths.
      use transportf_dep_assembly_mor.
    }
    cbn.
    etrans.
    {
      do 3 apply maponpaths.
      use eq_function_idtoiso_dep_assembly.
    }
    rewrite !(functtransportf (λ z, g(h z)) X).
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply setproperty.
  Qed.
  
  (** * 5. The comprehension functor *)

  (** * 5.1. The total assembly *)
  Section TotalAssembly.
    Context {Γ : assembly A}
            (X : dep_assembly Γ).

    Definition total_assembly
      : assembly A.
    Proof.
      use make_assembly.
      - exact (total2_hSet X).
      - exact (λ a xy, π₁ · a ⊩ pr1 xy ∧ π₂ · a ⊩ pr2 xy)%ca.
      - abstract
          (intros ;
           apply propproperty).
      - abstract
          (intros ( x & xx ) ;
           pose proof (assembly_realizes_el x) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros ( a₁ & p₁ ) ;
           pose proof (assembly_realizes_el xx) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros ( a₂ & p₂ ) ;
           use hinhpr ;
           refine (pair · a₁ · a₂ ,, _)%ca ;
           rewrite combinatory_algebra_pr1_pair ;
           rewrite combinatory_algebra_pr2_pair ;
           cbn ;
           exact (p₁ ,, p₂)).
    Defined.

    Definition total_assembly_pr
      : assembly_morphism total_assembly Γ.
    Proof.
      use make_assembly_morphism.
      - exact (λ xy, pr1 xy).
      - abstract
          (use hinhpr ;
           refine (π₁ ,, _) ;
           intros a x p ;
           exact (pr1 p)).
    Defined.

    Definition total_assembly_cod
      : disp_codomain (cat_of_assembly A) (functor_identity (cat_of_assembly A) Γ)
      := total_assembly ,, total_assembly_pr.
  End TotalAssembly.

  (** ** 5.2. The total assembly morphism *)
  Section TotalAssemblyMor.
    Context {Γ₁ Γ₂ : assembly A}
            {X₁ : dep_assembly Γ₁}
            {X₂ : dep_assembly Γ₂}
            {s : assembly_morphism Γ₁ Γ₂}
            (f : dep_assembly_morphism X₁ X₂ s).

    Definition total_assembly_morphism
      : assembly_morphism (total_assembly X₁) (total_assembly X₂).
    Proof.
      use make_assembly_morphism.
      - exact (λ xy, s (pr1 xy) ,, f (pr1 xy) (pr2 xy)).
      - abstract
          (pose proof (assembly_morphism_tracked s) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros ( a₁ & p₁ ) ;
           pose proof (dep_assembly_morphism_function_track f) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros ( a₂ & p₂ ) ;
           use hinhpr ;
           refine (pairf · (B · a₁ · π₁) · (Bt · a₂) ,, _)%ca ;
           intros b ( x & y ) ( q₁ & q₂ ) ;
           simpl ;
           rewrite combinatory_algebra_pr1_pair_fun ;
           rewrite combinatory_algebra_pr2_pair_fun ;
           rewrite !combinatory_algebra_b_eq ;
           rewrite combinatory_algebra_total_comp_eq ;
           exact (p₁ _ x q₁ ,, p₂ _ _ _ _ q₁ q₂)).
    Defined.

    Proposition total_assembly_morphism_comm
      : comp_assembly_morphism
          total_assembly_morphism
          (total_assembly_pr X₂)
        =
        comp_assembly_morphism (total_assembly_pr X₁) s.
    Proof.
      use assembly_morphism_eq.
      intros x ; cbn.
      apply idpath.
    Qed.

    Definition total_assembly_morphism_cod
      : total_assembly_cod X₁ -->[ s ] total_assembly_cod X₂
      := total_assembly_morphism ,, total_assembly_morphism_comm.
  End TotalAssemblyMor.

  (** ** 5.3. Comprehension of dependent assemblies *)
  Definition dep_assembly_comprehension_data
    : disp_functor_data
        (functor_identity _)
        disp_cat_of_dep_assembly
        (disp_codomain _).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ X, total_assembly_cod X).
    - intros Γ₁ Γ₂ X₁ X₂ s f.
      exact (total_assembly_morphism_cod f).
  Defined.

  Proposition dep_assembly_comprehension_laws
    : disp_functor_axioms dep_assembly_comprehension_data.
  Proof.
    split ; intros ; use eq_cod_mor ; rewrite transportb_cod_disp.
    - use assembly_morphism_eq.
      intro ; cbn.
      apply idpath.
    - use assembly_morphism_eq.
      intro ; cbn.
      apply idpath.
  Qed.
  
  Definition dep_assembly_comprehension
    : disp_functor
        (functor_identity _)
        disp_cat_of_dep_assembly
        (disp_codomain _).
  Proof.
    simple refine (_ ,, _).
    - exact dep_assembly_comprehension_data.
    - exact dep_assembly_comprehension_laws.
  Defined.

  (** * 6. The comprehension functor is fully faithful *)
  Definition cod_mor_to_dep_assembly_mor
             {Γ₁ Γ₂ : assembly A}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : assembly_morphism (total_assembly X₁) (total_assembly X₂))
             (p : comp_assembly_morphism f (total_assembly_pr X₂)
                  =
                  comp_assembly_morphism (total_assembly_pr X₁) s)
    : dep_assembly_morphism X₁ X₂ s.
  Proof.
    use make_dep_assembly_morphism.
    - intros x xx.
      exact (transportf
               X₂
               (assembly_morphism_eq_point p (x ,, xx))
               (pr2 (f (x ,, xx)))).
    - abstract
        (pose proof (assembly_morphism_tracked f) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros (a & Ha) ;
         use hinhpr ;
         refine (Ft · a ,, _)%ca ;
         intros x xx b₁ b₂ q₁ q₂ ;
         use dep_assembly_transportf_realizes ;
         rewrite combinatory_algebra_total_mor_eq ;
         refine (pr2 (Ha (pair · b₁ · b₂)%ca (x ,, xx) _)) ;
         simpl ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         exact (q₁ ,, q₂)).
  Defined.

  Proposition cod_mor_to_dep_assembly_mor_eq
              {Γ₁ Γ₂ : assembly A}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              (f : assembly_morphism (total_assembly X₁) (total_assembly X₂))
              (p : comp_assembly_morphism f (total_assembly_pr X₂)
                   =
                   comp_assembly_morphism (total_assembly_pr X₁) s)
    : total_assembly_morphism_cod (cod_mor_to_dep_assembly_mor f p) = f ,, p.
  Proof.
    use eq_cod_mor ; cbn.
    use assembly_morphism_eq.
    intro x.
    use total2_paths_f.
    - exact (!(assembly_morphism_eq_point p x)).
    - cbn.
      rewrite transport_f_f.
      rewrite pathsinv0r.
      apply idpath.
  Qed.
      
  Proposition disp_functor_ff_dep_assembly_comprehension
    : disp_functor_ff dep_assembly_comprehension.
  Proof.
    intros Γ₁ Γ₂ X₁ X₂ s.
    use isweq_iso.
    - intros fp.
      exact (cod_mor_to_dep_assembly_mor (pr1 fp) (pr2 fp)).
    - abstract
        (intros f ;
         use dep_assembly_morphism_eq ;
         intros x xx ; cbn ;
         use (transportf_set X₂) ;
         apply setproperty).
    - abstract
        (intros fp ;
         exact (cod_mor_to_dep_assembly_mor_eq (pr1 fp) (pr2 fp))).
  Defined.
  
  (** * 7. Comprehension preserves Cartesian morphisms *)
  Section TotalPullback.
    Context {Γ₁ Γ₂ : assembly A}
            (s : assembly_morphism Γ₁ Γ₂)
            (X : dep_assembly Γ₂).

    Section UMP.
      Context {X' : assembly A}
              {g : assembly_morphism X' (total_assembly X)}
              {h : assembly_morphism X' Γ₁}
              (p : comp_assembly_morphism g (total_assembly_pr X)
                   =
                   comp_assembly_morphism h s).

      Definition total_assembly_pullback_mor
        : assembly_morphism
            X'
            (total_assembly (dep_assembly_subst s X)).
      Proof.
        use make_assembly_morphism.
        - exact (λ x,
                 h x
                 ,,
                 transportf X (assembly_morphism_eq_point p x) (pr2 (g x))).
        - abstract
            (pose proof (assembly_morphism_tracked h) as q ;
             revert q ;
             use factor_through_squash_hProp ;
             intros ( a₁ & q₁ ) ;
             pose proof (assembly_morphism_tracked g) as q ;
             revert q ;
             use factor_through_squash_hProp ;
             intros ( a₂ & q₂ ) ;
             use hinhpr ;
             refine (pairf · a₁ · (B · π₂ · a₂) ,, _)%ca ;
             intros b w r ;
             simpl ;
             rewrite combinatory_algebra_pr1_pair_fun ;
             rewrite combinatory_algebra_pr2_pair_fun ;
             rewrite combinatory_algebra_b_eq ;
             refine (q₁ b w r ,, _) ;
             pose (pr2 (q₂ b _ r)) as r' ;
             exact (dep_assembly_transportf_realizes _ r')).
      Defined.

      Proposition total_assembly_pullback_mor_pr1
        : comp_assembly_morphism
            total_assembly_pullback_mor
            (total_assembly_morphism (dep_assembly_subst_mor s X))
          =
          g.
      Proof.
        use assembly_morphism_eq.
        intro x.
        use total2_paths_f.
        - exact (!(assembly_morphism_eq_point p x)).
        - cbn.
          rewrite transport_f_f.
          rewrite pathsinv0r.
          apply idpath.
      Qed.

      Proposition total_assembly_pullback_unique
        : isaprop
            (∑ hk,
             (comp_assembly_morphism
                hk
                (total_assembly_morphism (dep_assembly_subst_mor s X))
              =
              g)
             ×
             comp_assembly_morphism hk (total_assembly_pr (λ x : Γ₁, X (s x))) = h).
      Proof.
        use invproofirrelevance.
        intros f₁ f₂.
        use subtypePath.
        {
          intro.
          use isapropdirprod ; apply isaset_assembly_morphism.
        }
        use assembly_morphism_eq.
        intro x.
        pose (q₁ := fiber_paths (assembly_morphism_eq_point (pr12 f₁ @ !(pr12 f₂)) x)).
        pose (q₂ := assembly_morphism_eq_point (pr22 f₁ @ !(pr22 f₂)) x).
        cbn in q₁, q₂.
        use total2_paths_f.
        - exact q₂.
        - refine (_ @ q₁).
          rewrite transportf_dep_assembly_subst.
          apply maponpaths_2.
          apply setproperty.
      Qed.
    End UMP.
      
    Definition total_assembly_pullback
      : isPullback
          (C := cat_of_assembly A)
          (total_assembly_morphism_comm (dep_assembly_subst_mor s X)).
    Proof.
      intros X' g h p.
      use iscontraprop1.
      - exact total_assembly_pullback_unique.
      - simple refine (_ ,, _ ,, _).
        + exact (total_assembly_pullback_mor p).
        + exact (total_assembly_pullback_mor_pr1 p).
        + abstract
            (use assembly_morphism_eq ;
             intro x ; cbn ;
             apply idpath).
    Defined.
  End TotalPullback.
  
  Proposition is_cartesian_dep_assembly_comprehension
    : is_cartesian_disp_functor dep_assembly_comprehension.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      apply dep_assembly_cleaving.
    }
    intros Γ₁ Γ₂ s X.
    use isPullback_cartesian_in_cod_disp.
    apply total_assembly_pullback.
  Defined.

  (** * 8. The comprehension category of assemblies *)
  Definition assembly_comprehension_cat
    : comprehension_cat_structure (cat_of_assembly A)
    := disp_cat_of_dep_assembly
       ,,
       dep_assembly_cleaving
       ,,
       dep_assembly_comprehension
       ,,
       is_cartesian_dep_assembly_comprehension.

  (** * 9. The fiberwise terminal object *)
  Section FiberwiseTerminal.
    Context (Γ : assembly A).

    Definition terminal_dep_assembly
      : dep_assembly Γ
      := λ _, terminal_assembly A.

    Definition terminal_dep_assembly_morphism
               (X : dep_assembly Γ)
      : dep_assembly_morphism
          X
          terminal_dep_assembly
          (id_assembly_morphism Γ).
    Proof.
      use make_dep_assembly_morphism.
      - exact (λ _ _, tt).
      - abstract
          (use hinhpr ;
           refine (I ,, _) ;
           intros ; cbn ;
           exact tt).
    Defined.
    
    Definition fiberwise_terminal_object_dep_assembly
      : Terminal disp_cat_of_dep_assembly[{Γ}].
    Proof.
      use make_Terminal.
      - exact terminal_dep_assembly.
      - intros X.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros f₁ f₂ ;
             use dep_assembly_morphism_eq ;
             intros x xx ;
             apply isapropunit).
        + exact (terminal_dep_assembly_morphism X).
    Defined.
  End FiberwiseTerminal.

  Definition fiberwise_terminal_dep_assembly
    : fiberwise_terminal dep_assembly_cleaving.
  Proof.
    split.
    - exact fiberwise_terminal_object_dep_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         use (preserves_terminal_if_preserves_chosen
                (fiberwise_terminal_object_dep_assembly Γ₂)) ;
         apply fiberwise_terminal_object_dep_assembly).
  Defined.

  Definition fiberwise_terminal_z_iso_inv
             (Γ : assembly A)
    : assembly_morphism
        Γ
        (total_assembly (terminal_dep_assembly Γ)).
  Proof.
    use make_assembly_morphism.
    - exact (λ x, x ,, tt).
    - abstract
        (use hinhpr ;
         refine (pair_s · I ,, _)%ca ;
         intros a x p ;
         refine (_ ,, tt) ;
         simpl ;
         rewrite combinatory_algebra_pr1_pair_s ;
         exact p).
  Defined.
  
  Definition fiberwise_terminal_z_iso
             (Γ : assembly A)
    : is_z_isomorphism
        (C := cat_of_assembly A)
        (total_assembly_pr (terminal_dep_assembly Γ)).
  Proof.
    use make_is_z_isomorphism.
    - exact (fiberwise_terminal_z_iso_inv Γ).
    - abstract
        (split ; use assembly_morphism_eq ; intro ; cbn ; [ | apply idpath ] ;
         use subtypePath ; [ intro ; apply isapropunit | ] ;
         apply idpath).
  Defined.
End DependentAssembly.

Arguments disp_cat_of_dep_assembly_ob_mor : clear implicits.
Arguments disp_cat_of_dep_assembly_id_comp : clear implicits.
Arguments disp_cat_of_dep_assembly_data : clear implicits.
Arguments disp_cat_of_dep_assembly_axioms : clear implicits.
Arguments disp_cat_of_dep_assembly : clear implicits.
Arguments dep_assembly_subst /.
Arguments dep_assembly_cleaving : clear implicits.
Arguments dep_assembly_comprehension_data : clear implicits.
Arguments dep_assembly_comprehension_laws : clear implicits.
Arguments dep_assembly_comprehension : clear implicits.
Arguments disp_functor_ff_dep_assembly_comprehension : clear implicits.
Arguments assembly_comprehension_cat : clear implicits.
Arguments fiberwise_terminal_dep_assembly : clear implicits.
