(**

 The comprehension category of assemblies and its strictification

 In this file, we construct the strictification of the comprehension category of assemblies.
 To do so, we first give a slightly different construction of type formers in the
 comprehension category of assemblies. Rather than interpreting quantifiers as adjoints, we
 use the description of type formers as given by Lumsdaine and Warren.

 The main content of this files is about the construction of the universe. To do so, we need
 to give a set `u` and a map `el` from `u` to assemblies. The universe is then interpreted as
 the discrete assembly on `u`, and `el` allows us to map terms of the universe to types. We
 show that if there is an element `un : u` such that `el un` is isomorphic to the unit
 assembly, then the resulting universe in the comprehension category of assemblies contains
 the unit type. We do not give such conditions for ∑-types or ∏-types: instead, to verify
 that some universe is closed under ∑-types or ∏-types, we would use verify that directly.
 The reason is that we would like to reduce a closure condition to types in the empty context,
 but such a condition cannot be extended to types in arbitrary contexts, as for arbitrary
 contexts one needs a strong realizability condition for the isomorphism.

 The following has to be noted about universes of assemblies. To express that the universe
 is closed under some type former, we use isomorphisms of assemblies. For instance, to say
 that a universe is closed under ∑-types, we say that we have an isomorphism between the
 assemblies `el(∑ a b)` and `∑ (el a) (el b)`. However, this adds a complication: if we want
 to lift a universe of sets to a universe of assemblies, then, in general, we only have an
 isomorphism of sets between `el(∑ a b)` and `∑ (el a) (el b)`, and there is no reason why
 this isomorphism should have a realizer. If we use the universe of iterative sets or an
 inductive-recursive universe, then `el(∑ a b)` and `∑ (el a) (el b)` are equal, and we can
 use the identity isomorphism to say that `u` is closed under ∑-types. Since the identity
 has a realizer, we can use both inductive recursive universes and the universe of iterative
 sets to construct a universe of assemblies that is closed under ∑-types.

 For ∏-types there is an additional complication. To construct ∏-types in the comprehension
 category of assemblies, we need to take a subtype of the ∏-type of sets. Specifically, the
 type `∏ X₁ X₂` consists of all function `∏ (x : X₁), X₂ x` for which there exists a realizer
 that tracks this function. If we want to construct a universe of assemblies that is closed
 under ∏-types, then our universe needs to be closed under suitable subtypes as well. We can
 guarantee this closure condition, for instance, by requiring that every proposition is
 contained in the universe. Note that this condition is impredicative, and to get actual
 universes that satisfy this assumption, we need propositional resizing in the metatheory.

 Other important types in the comprehension category of assemblies are the impredicative
 universes, namely the assembly of PERs (impredicative universe of sets) and the powerset
 fo the combinatory algebra (impredicatve universe of propositions). To guarantee that our
 universe contains these assemblies, we need further assumptions, namely that our universe
 contains the combinatory algebra, the type of propositions, and every proposition. PERs are
 defined to be relations on the combinatory algebra that are symmetric and transitive, so the
 aforementioned requirements are sufficient to guarantee that our universe contains the
 assembly of PERs. The universe of propositions is defined to be the power set of the
 combinatory algebra, which is contained in the universe if it contains `hProp`.

 Content
 1. The comprehension category of assemblies
 2. Calculational lemmas for the comprehension category of assemblies
 3. ∑-types of assemblies
 4. Unit types of assemblies
 5. ∏-types of assemblies
 6. Universes of assemblies
 7. Construction of the universe in the comprehension category of assemblies
 8. The universe contains the unit type
 9. The strictification of the comprehension category of assemblies

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.SectionsExamples.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCats.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatTypeFormers.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatUniverse.
Require Import UniMath.CategoryTheory.ComprehensionCats.CwfFromCompCatWithUniv.
Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFams.

Require Import Basics.BIAlgebra.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Types.Terms.

Local Open Scope cat.
Local Open Scope ca.
Local Open Scope assembly.

Section AssemblyCompCat.
  Context (A : combinatory_algebra).

  (** * 1. The comprehension category of assemblies *)
  Definition assembly_comp_cat_data
    : comp_cat.
  Proof.
    simple refine (_ ,, _).
    - exact (cat_of_assembly A).
    - simple refine (_ ,, _ ,, _ ,, _).
      + exact (disp_cat_of_dep_assembly A).
      + exact (dep_assembly_cleaving A).
      + exact (dep_assembly_comprehension A).
      + exact is_cartesian_dep_assembly_comprehension.
  Defined.

  Definition assembly_comp_cat
    : comp_cat_with_terminal.
  Proof.
    simple refine (_ ,, _).
    - exact assembly_comp_cat_data.
    - exact (terminal_cat_of_assembly A).
  Defined.

  (** * 2. Calculational lemmas for the comprehension category of assemblies *)
  Proposition assembly_comp_cat_subst_ty_iso
              {Γ Δ : assembly A}
              (X : dep_assembly Δ)
              {s₁ s₂ : assembly_morphism Γ Δ}
              (p : s₁ = s₂)
              {γ : Γ}
              (x : X (s₁ γ))
    : pr11 (comp_cat_subst_ty_iso (C := assembly_comp_cat) X p) γ x
      =
      transportf X (assembly_morphism_eq_point p γ) x.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition assembly_comp_cat_subst_ty_id_iso
              {Γ : assembly A}
              (X : dep_assembly Γ)
              {γ : Γ}
              (x : X γ)
    : pr11 (comp_cat_subst_ty_id_iso (C := assembly_comp_cat) X) γ x = x.
  Proof.
    cbn.
    etrans.
    {
      apply (transportb_dep_assembly_mor
               (fiber_functor_from_cleaving_identity_data_subproof _)).
    }
    use (transportf_set X).
    apply setproperty.
  Qed.

  Proposition assembly_comp_cat_subst_ty_comp_iso
              {Γ₁ Γ₂ Γ₃ : assembly A}
              (X : dep_assembly Γ₃)
              (s₁ : assembly_morphism Γ₁ Γ₂)
              (s₂ : assembly_morphism Γ₂ Γ₃)
              {γ : Γ₁}
              (x : X (s₂ (s₁ γ)))
    : pr11 (comp_cat_subst_ty_comp_iso (C := assembly_comp_cat) X s₂ s₁) γ x = x.
  Proof.
    cbn.
    etrans.
    {
      apply (transportb_dep_assembly_mor
               (fiber_functor_from_cleaving_comp_data_subproof _ _)).
    }
    use (transportf_set X).
    apply setproperty.
  Qed.

  Proposition coerce_assembly_comp_cat
              {Γ : assembly A}
              {X₁ X₂ : dep_assembly Γ}
              (f : dep_assembly_morphism X₁ X₂ (id_assembly_morphism _))
              (t : assembly_term X₁)
    : coerce_comp_cat_tm
        (C := assembly_comp_cat)
        f
        (assembly_term_to_section X₁ t)
      =
      assembly_term_to_section _ (coerce_assembly_term f t).
  Proof.
    use comp_cat_tm_eq.
    use assembly_morphism_eq.
    intro γ.
    cbn.
    apply idpath.
  Qed.

  Proposition assembly_comp_cat_reindex_iso
              {Γ Δ : assembly A}
              (s : assembly_morphism Γ Δ)
              {X₁ X₂ : dep_assembly Δ}
              (f : z_iso
                     (C := fiber_category (disp_cat_of_dep_assembly A) _)
                     X₁ X₂)
              {γ : Γ}
              (x : X₁ (s γ))
    : pr11 (comp_cat_reindex_iso (C := assembly_comp_cat) s f) γ x
      =
      pr11 f (s γ) x.
  Proof.
    cbn.
    etrans.
    {
      apply (transportf_dep_assembly_mor (id_right _ @ !(id_left _))).
    }
    use (transportf_set X₂).
    apply setproperty.
  Qed.

  Proposition subst_tm_assembly_comp_cat
              {Γ Δ : assembly A}
              (s : assembly_morphism Γ Δ)
              {X : dep_assembly Δ}
              (t : assembly_term X)
    : comp_cat_subst_tm (C := assembly_comp_cat) s (assembly_term_to_section _ t)
      =
      assembly_term_to_section _ (subst_assembly_term s t).
  Proof.
    use comp_cat_tm_eq.
    refine (!_).
    use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
    - use assembly_morphism_eq.
      intro γ.
      cbn.
      apply idpath.
    - use assembly_morphism_eq.
      intro γ.
      cbn.
      apply idpath.
  Qed.

  Proposition subst_tm_assembly_comp_cat_alt
              {Γ Δ : assembly A}
              (s : assembly_morphism Γ Δ)
              {X : dep_assembly Δ}
              (t : comp_cat_tm (C := assembly_comp_cat) X)
    : section_to_assembly_term _ (comp_cat_subst_tm (C := assembly_comp_cat) s t)
      =
      subst_assembly_term s (section_to_assembly_term _ t).
  Proof.
    refine (_ @ homotinvweqweq (assembly_term_weq_section _) _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      exact (!(homotweqinvweq (assembly_term_weq_section _) t)).
    }
    apply subst_tm_assembly_comp_cat.
  Qed.

  (** * 3. ∑-types of assemblies *)
  Definition sigma_assembly
             (Γ : assembly A)
             (X₁ : dep_assembly Γ)
             (X₂ : dep_assembly (total_assembly X₁))
    : dep_assembly Γ.
  Proof.
    intro γ.
    exact (total_assembly (λ (x : X₁ γ), X₂ (γ ,, x))).
  Defined.

  Definition sigma_assembly_pair_realizer
    : A
    := Λ (Co pair • (Co π₁ • (Co π₁ • V 0))
                  • (Co pair • (Co π₂ • (Co π₁ • V 0)) • (Co π₂ • V 0))).

  Proposition sigma_assembly_pair_realizer_eq
              (a : A)
    : sigma_assembly_pair_realizer · a
      =
      pair · (π₁ · (π₁ · a)) · (pair · (π₂ · (π₁ · a)) · (π₂ · a)).
  Proof.
    unfold sigma_assembly_pair_realizer.
    etrans.
    {
      apply lam_term_single.
    }
    cbn.
    apply idpath.
  Qed.

  Definition sigma_assembly_pair
             (Γ : assembly A)
             (X₁ : dep_assembly Γ)
             (X₂ : dep_assembly (total_assembly X₁))
    : assembly_morphism
        (total_assembly X₂)
        (total_assembly (sigma_assembly Γ X₁ X₂)).
  Proof.
    use make_assembly_morphism.
    - exact (λ γxy, pr11 γxy ,, pr21 γxy ,, pr2 γxy).
    - abstract
        (use hinhpr ;
         refine (sigma_assembly_pair_realizer ,, _) ;
         intros a ((γ & x) & y) ((p₁ & p₂) & p₃) ;
         rewrite sigma_assembly_pair_realizer_eq ;
         cbn in * ;
         rewrite !combinatory_algebra_pr1_pair ;
         rewrite !combinatory_algebra_pr2_pair ;
         rewrite !combinatory_algebra_pr1_pair ;
         exact (p₁ ,, p₂ ,, p₃)).
  Defined.

  Definition sigma_assembly_proj_realizer
    : A
    := Λ (Co pair • (Co pair • (Co π₁ • V 0) • (Co π₁ • (Co π₂ • V 0)))
                  • (Co π₂ • (Co π₂ • V 0))).

  Proposition sigma_assembly_proj_realizer_eq
              (a : A)
    : sigma_assembly_proj_realizer · a
      =
      pair · (pair · (π₁ · a) · (π₁ · (π₂ · a))) · (π₂ · (π₂ · a)).
  Proof.
    unfold sigma_assembly_proj_realizer.
    etrans.
    {
      apply lam_term_single.
    }
    cbn.
    apply idpath.
  Qed.

  Definition sigma_assembly_proj
             (Γ : assembly A)
             (X₁ : dep_assembly Γ)
             (X₂ : dep_assembly (total_assembly X₁))
    : assembly_morphism
        (total_assembly (sigma_assembly Γ X₁ X₂))
        (total_assembly X₂).
  Proof.
    use make_assembly_morphism.
    - exact (λ γxy, (pr1 γxy ,, pr12 γxy) ,, pr22 γxy).
    - abstract
        (use hinhpr ;
         refine (sigma_assembly_proj_realizer ,, _) ;
         intros a (γ & x & y) (p₁ & p₂ & p₃) ;
         rewrite sigma_assembly_proj_realizer_eq ;
         cbn in * ;
         rewrite !combinatory_algebra_pr1_pair ;
         rewrite !combinatory_algebra_pr2_pair ;
         exact ((p₁ ,, p₂) ,, p₃)).
  Defined.

  Definition assembly_comp_cat_sigma_stable
             (Γ Δ : assembly A)
             (s : assembly_morphism Δ Γ)
             (X₁ : dep_assembly Γ)
             (X₂ : dep_assembly (total_assembly X₁))
    : z_iso
        (C := fiber_category (disp_cat_of_dep_assembly A) _)
        (λ x, sigma_assembly Γ X₁ X₂ (s x))
        (sigma_assembly Δ (λ x, X₁ (s x)) (λ x, X₂ (s (pr1 x) ,, pr2 x))).
  Proof.
    use make_z_iso.
    - use make_dep_assembly_morphism.
      + exact (λ δ xy, xy).
      + abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros δ xy a₁ a₂ p₁ p₂ ;
           cbn in * ;
           rewrite combinatory_algebra_ks_eq ;
           exact p₂).
    - use make_dep_assembly_morphism.
      + exact (λ δ xy, xy).
      + abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros δ xy a₁ a₂ p₁ p₂ ;
           cbn in * ;
           rewrite combinatory_algebra_ks_eq ;
           exact p₂).
    - abstract
        (split ;
         use dep_assembly_morphism_eq ;
         intros δ xy ;
         exact (fiber_comp_dep_assembly _ _ _)).
  Defined.

  Definition assembly_comp_cat_sigma
    : comp_cat_sigma assembly_comp_cat.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact sigma_assembly.
    - exact sigma_assembly_pair.
    - abstract
        (intros Γ X₁ X₂ ;
         use assembly_morphism_eq ;
         intro ; cbn ;
         apply idpath).
    - exact sigma_assembly_proj.
    - abstract
        (intros Γ X₁ X₂ ;
         use assembly_morphism_eq ;
         intro ; cbn ;
         apply idpath).
    - abstract
        (intros Γ X₁ X₂ ;
         use assembly_morphism_eq ;
         intro ; cbn ;
         apply idpath).
    - exact assembly_comp_cat_sigma_stable.
    - abstract
        (intros Γ Δ s X₁ X₂ ;
         use assembly_morphism_eq ;
         intros x ;
         cbn ;
         apply idpath).
  Defined.

  (** * 4. Unit types of assemblies *)
  Definition assembly_unit_tt
             (Γ : assembly A)
    : assembly_term (terminal_dep_assembly Γ).
  Proof.
    use make_assembly_term.
    - exact (λ γ, tt).
    - abstract
        (use hinhpr ;
         refine (I ,, _) ;
         cbn ;
         intros ;
         exact tt).
  Defined.

  Definition TODO { Z : UU } : Z.
  Admitted.

  Definition assembly_unit_subst
             (Γ Δ : assembly A)
             (s : assembly_morphism Γ Δ)
    : z_iso
        (C := fiber_category (disp_cat_of_dep_assembly A) _)
        (λ x, terminal_dep_assembly Δ (s x))
        (terminal_dep_assembly Γ).
  Proof.
    use make_z_iso.
    - use make_dep_assembly_morphism.
      + exact (λ γ x, x).
      + abstract
          (use hinhpr ;
           refine (I ,, _) ;
           intro ; intros ;
           exact tt).
    - use make_dep_assembly_morphism.
      + exact (λ γ x, x).
      + abstract
          (use hinhpr ;
           refine (I ,, _) ;
           intro ; intros ;
           exact tt).
    - abstract
        (split ;
         use dep_assembly_morphism_eq ;
         intros γ x ;
         apply isapropunit).
  Defined.

  Definition assembly_comp_cat_unit
    : comp_cat_unit assembly_comp_cat.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact terminal_dep_assembly.
    - intros Γ.
      use assembly_term_to_section.
      exact (assembly_unit_tt Γ).
    - apply TODO.
    - apply TODO.
    - abstract
        (intros Γ t ;
         refine (!(homotweqinvweq (assembly_term_weq_section _) t) @ _) ;
         apply maponpaths ;
         cbn ;
         use assembly_term_eq ;
         intro x ;
         apply isapropunit).
    - exact assembly_unit_subst.
    - apply TODO.
    - apply TODO.
  Defined.

  (** * 5. ∏-types of assemblies *)
  Definition assembly_dep_mor_tracker
             {Γ : assembly A}
             {X₁ : dep_assembly Γ}
             {X₂ : dep_assembly (total_assembly X₁)}
             {γ : Γ}
             (a : A)
             (f : ∏ (x : X₁ γ), X₂ (γ ,, x))
    : hProp
    := (∀ (x : X₁ γ) (b : A), b ⊩ x ⇒ a · b ⊩ f x)%logic.

  Definition assembly_dep_mor
             {Γ : assembly A}
             (X₁ : dep_assembly Γ)
             (X₂ : dep_assembly (total_assembly X₁))
             (γ : Γ)
    : UU
    := ∑ (f : ∏ (x : X₁ γ), X₂ (γ ,, x)),
       ∃ (a : A), assembly_dep_mor_tracker a f.

  Definition make_assembly_dep_mor
             {Γ : assembly A}
             {X₁ : dep_assembly Γ}
             {X₂ : dep_assembly (total_assembly X₁)}
             {γ : Γ}
             (f : ∏ (x : X₁ γ), X₂ (γ ,, x))
             (H : ∃ (a : A), assembly_dep_mor_tracker a f)
    : assembly_dep_mor X₁ X₂ γ
    := f ,, H.
             
  Definition assembly_dep_mor_fun
             {Γ : assembly A}
             {X₁ : dep_assembly Γ}
             {X₂ : dep_assembly (total_assembly X₁)}
             {γ : Γ}
             (f : assembly_dep_mor X₁ X₂ γ)
    : ∏ (x : X₁ γ), X₂ (γ ,, x)
    := pr1 f.

  Coercion assembly_dep_mor_fun : assembly_dep_mor >-> Funclass.

  Proposition tracker_of_assembly_dep_mor
              {Γ : assembly A}
              {X₁ : dep_assembly Γ}
              {X₂ : dep_assembly (total_assembly X₁)}
              {γ : Γ}
              (f : assembly_dep_mor X₁ X₂ γ)
    : ∃ (a : A), assembly_dep_mor_tracker a f.
  Proof.
    exact (pr2 f).
  Defined.

  Proposition assembly_dep_mor_eq
              {Γ : assembly A}
              {X₁ : dep_assembly Γ}
              {X₂ : dep_assembly (total_assembly X₁)}
              {γ : Γ}
              {f g : assembly_dep_mor X₁ X₂ γ}
              (p : ∏ (x : X₁ γ), f x = g x)
    : f = g.
  Proof.
    use subtypePath.
    {
      intro.
      apply propproperty.
    }
    use funextsec.
    intro x.
    exact (p x).
  Qed.
  
  Definition pi_assembly
             (Γ : assembly A)
             (X₁ : dep_assembly Γ)
             (X₂ : dep_assembly (total_assembly X₁))
             (γ : Γ)
    : assembly A.
  Proof.
    use make_assembly'.
    - use make_hSet.
      + exact (assembly_dep_mor X₁ X₂ γ).
      + abstract
          (use isaset_total2 ; [ use impred_isaset ; intro ; apply setproperty | ] ;
           intro ;
           apply isasetaprop ;
           apply propproperty).
    - exact (λ a f, assembly_dep_mor_tracker a (pr1 f)).
    - intro f.
      exact (tracker_of_assembly_dep_mor f).
  Defined.

  Definition combinatory_algebra_lam_realizer
    : A
    := Λ (V 0 • (Co pair • V 1 • V 2)).
  
  Proposition combinatory_algebra_lam_realizer_eq
              (a₁ a₂ a₃ : A)
    : combinatory_algebra_lam_realizer · a₁ · a₂ · a₃
      =
      a₁ · (pair · a₂ · a₃).
  Proof.
    unfold combinatory_algebra_lam_realizer.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply lam_term_multiple.
    }
    etrans.
    {
      apply maponpaths_2.
      apply lam_term_multiple.
    }
    etrans.
    {
      apply lam_term_single.
    }
    simpl.
    apply idpath.
  Qed.

  Definition assembly_dep_mor_lam
             {Γ : assembly A}
             {X₁ : dep_assembly Γ}
             {X₂ : dep_assembly (total_assembly X₁)}
             (t : assembly_term X₂)
    : assembly_term (pi_assembly Γ X₁ X₂).
  Proof.
    use make_assembly_term.
    - intro γ.
      use make_assembly_dep_mor.
      + exact (λ x, t (γ ,, x)).
      + abstract
          (pose proof (assembly_term_tracker t) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a & p) ;
           pose proof (assembly_realizes_el γ) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros (b & q) ;
           use hinhpr ;
           refine (B · a · (pair · b) ,, _) ;
           intros x c r ;
           cbn ;
           rewrite combinatory_algebra_b_eq ;
           apply p ;
           split ;
           [ rewrite  combinatory_algebra_pr1_pair ;
             exact q
           | rewrite combinatory_algebra_pr2_pair ;
             exact r ]).
    - abstract
        (pose proof (assembly_term_tracker t) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros (a & p) ;
         use hinhpr ;
         refine (combinatory_algebra_lam_realizer · a ,, _) ;
         intros b γ q x c r ;
         rewrite combinatory_algebra_lam_realizer_eq ;
         apply p ;
         cbn ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         exact (q ,, r)).
  Defined.

  Definition assembly_dep_mor_app_realizer
    : A
    := Λ (V 0 • (Co π₁ • V 1) • (Co π₂ • V 1)).

  Proposition assembly_dep_mor_app_realizer_eq
              (a b : A)
    : assembly_dep_mor_app_realizer · a · b = a · (π₁ · b) · (π₂ · b).
  Proof.
    unfold assembly_dep_mor_app_realizer.
    etrans.
    {
      apply maponpaths_2.
      apply lam_term_multiple.
    }
    etrans.
    {
      apply lam_term_single.
    }
    simpl.
    apply idpath.
  Qed.
              
  Definition assembly_dep_mor_app
             {Γ : assembly A}
             {X₁ : dep_assembly Γ}
             {X₂ : dep_assembly (total_assembly X₁)}
             (t : assembly_term (pi_assembly Γ X₁ X₂))
    : assembly_term X₂.
  Proof.
    use make_assembly_term.
    - exact (λ γ, pr1 (t (pr1 γ)) (pr2 γ)).
    - abstract
        (pose proof (assembly_term_tracker t) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros (a & p) ;
         use hinhpr ;
         refine (assembly_dep_mor_app_realizer · a ,, _) ;
         intros b (x & y) (q₁ & q₂) ;
         rewrite assembly_dep_mor_app_realizer_eq ;
         cbn in * ;
         exact (p (π₁ · b) x q₁ y (π₂ · b) q₂)).
  Defined.

  Definition assembly_comp_cat_pi_stable
             (Γ Δ : assembly A)
             (s : assembly_morphism Δ Γ)
             (X₁ : dep_assembly Γ)
             (X₂ : dep_assembly (total_assembly X₁))
    : z_iso
        (C := fiber_category (disp_cat_of_dep_assembly A) _)
        (λ x, pi_assembly Γ X₁ X₂ (s x))
        (pi_assembly Δ (λ x, X₁ (s x)) (λ x, X₂ (s (pr1 x) ,, pr2 x))).
  Proof.
    use make_z_iso.
    - use make_dep_assembly_morphism.
      + exact (λ δ f, f).
      + abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros δ x a₁ a₂ p q ;
           rewrite combinatory_algebra_ks_eq ;
           exact q).
    - use make_dep_assembly_morphism.
      + exact (λ δ f, f).
      + abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros δ x a₁ a₂ p q ;
           rewrite combinatory_algebra_ks_eq ;
           exact q).
    - abstract
        (split ;
         use dep_assembly_morphism_eq ;
         intros δ xy ;
         exact (fiber_comp_dep_assembly _ _ _)).
  Defined.
  
  Definition assembly_comp_cat_pi
    : comp_cat_pi assembly_comp_cat.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact pi_assembly.
    - intros Γ X₁ X₂ t.
      use assembly_term_to_section.
      exact (assembly_dep_mor_lam (section_to_assembly_term _ t)).
    - intros Γ X₁ X₂ t.
      use assembly_term_to_section.
      exact (assembly_dep_mor_app (section_to_assembly_term _ t)).
    - abstract
        (intros Γ X₁ X₂ t ;
         refine (_ @ homotweqinvweq (assembly_term_weq_section _) t) ;
         apply maponpaths ;
         use assembly_term_eq ;
         intros (γ & x) ;
         unfold assembly_dep_mor_lam ;
         cbn -[section_to_assembly_term] ;
         etrans ;
         [ refine (maponpaths (λ z, pr1 z x) _) ;
           refine (maponpaths (λ z, pr1 z γ) _) ;
           exact (homotinvweqweq (assembly_term_weq_section (pi_assembly Γ X₁ X₂)) _)
         | ] ;
         cbn ;
         apply idpath).
    - abstract
        (intros Γ X₁ X₂ t ;
         refine (_ @ homotweqinvweq (assembly_term_weq_section _) t) ;
         apply maponpaths ;
         use assembly_term_eq ;
         intros γ ;
         use assembly_dep_mor_eq ;
         intro x ;
         cbn -[section_to_assembly_term] ;
         exact (toforallpaths
                  _ _ _
                  (maponpaths
                     pr1
                     (homotinvweqweq
                        (assembly_term_weq_section X₂)
                        (assembly_dep_mor_app
                           (section_to_assembly_term (pi_assembly Γ X₁ X₂) t))))
                  (γ ,, x))).
    - exact assembly_comp_cat_pi_stable.
    - abstract
        (intros Γ Δ s X₁ X₂ t ;
         refine (_ @ homotweqinvweq (assembly_term_weq_section _) _) ;
         rewrite coerce_assembly_comp_cat ;
         rewrite subst_tm_assembly_comp_cat ;
         rewrite subst_tm_assembly_comp_cat_alt ;
         apply maponpaths ;
         refine (_ @ !(homotinvweqweq (assembly_term_weq_section _) _)) ;
         use assembly_term_eq ;
         intro γ ;
         use assembly_dep_mor_eq ;
         intros x ;
         cbn -[section_to_assembly_term] ;
         apply idpath).
  Defined.

  (** * 6. Universes of assemblies *)
  Definition assembly_universe
    : UU
    := ∑ (u : hSet), u → assembly A.

  Coercion assembly_universe_to_univ
           (u : assembly_universe)
    : hSet
    := pr1 u.

  Definition assembly_universe_el
             {u : assembly_universe}
    : u → assembly A
    := pr2 u.

  Definition assembly_universe_eq
             {u : assembly_universe}
             {x y : u}
             (p : x = y)
    : assembly_morphism
        (assembly_universe_el x)
        (assembly_universe_el y).
  Proof.
    induction p.
    apply id_assembly_morphism.
  Defined.

  Proposition realizes_assembly_universe_eq
              {u : assembly_universe}
              {x y : u}
              (p : x = y)
              {a : A}
              {e : assembly_universe_el x}
              (q : a ⊩ e)
    : a ⊩ assembly_universe_eq p e.
  Proof.
    induction p ; cbn.
    exact q.
  Qed.
  
  Proposition assembly_universe_eq_idpath
              {u : assembly_universe}
              (x : u)
              (e : assembly_universe_el x)
    : assembly_universe_eq (idpath _) e = e.
  Proof.
    apply idpath.
  Qed.
  
  Proposition assembly_universe_eq_loop
              {u : assembly_universe}
              (x : u)
              (p : x = x)
              (e : assembly_universe_el x)
    : assembly_universe_eq p e = e.
  Proof.
    assert (p = idpath _) as -> by apply setproperty.
    apply idpath.
  Qed.
  
  Proposition assembly_universe_eq_comp
              {u : assembly_universe}
              {x y z : u}
              (p : x = y)
              (q : y = z)
              (e : assembly_universe_el x)
    : assembly_universe_eq (p @ q) e
      =
      assembly_universe_eq q (assembly_universe_eq p e).
  Proof.
    induction p, q.
    apply idpath.
  Qed.

  Proposition assembly_universe_eq_path
              {u : assembly_universe}
              {x y : u}
              (p q : x = y)
              (e : assembly_universe_el x)
    : assembly_universe_eq p e = assembly_universe_eq q e.
  Proof.
    refine (maponpaths (λ z, z e) _).
    do 2 apply maponpaths.
    apply setproperty.
  Qed.

  Definition assembly_universe_contains_unit
             (u : assembly_universe)
    : UU
    := ∑ (un : u),
       z_iso
         (C := cat_of_assembly _)
         (assembly_universe_el un)
         (terminal_assembly _).

  Definition make_assembly_universe_contains_unit
             {u : assembly_universe}
             (un : u)
             (f : z_iso
                    (C := cat_of_assembly _)
                    (assembly_universe_el un)
                    (terminal_assembly _))
    : assembly_universe_contains_unit u
    := un ,, f.

  Coercion assembly_universe_contains_unit_code
           {u : assembly_universe}
           (un : assembly_universe_contains_unit u)
    : u
    := pr1 un.

  Definition assembly_universe_contains_unit_iso
             {u : assembly_universe}
             (un : assembly_universe_contains_unit u)
    : z_iso
        (C := cat_of_assembly _)
        (assembly_universe_el un)
        (terminal_assembly _)
    := pr2 un.

  Definition assembly_universe_contains_unit_iso_mor
             {u : assembly_universe}
             (un : assembly_universe_contains_unit u)
    : assembly_morphism
        (assembly_universe_el un)
        (terminal_assembly _)
    := pr1 (assembly_universe_contains_unit_iso un).

  Definition assembly_universe_contains_unit_iso_inv
             {u : assembly_universe}
             (un : assembly_universe_contains_unit u)
    : assembly_morphism
        (terminal_assembly _)
        (assembly_universe_el un)
    := inv_from_z_iso (assembly_universe_contains_unit_iso un).

  Proposition assembly_universe_contains_unit_iso_mor_inv
              {u : assembly_universe}
              (un : assembly_universe_contains_unit u)
              (x : unit)
    : assembly_universe_contains_unit_iso_mor
        un
        (assembly_universe_contains_unit_iso_inv un x)
      =
      x.
  Proof.
    apply isapropunit.
  Qed.

  Proposition assembly_universe_contains_unit_iso_inv_mor
              {u : assembly_universe}
              (un : assembly_universe_contains_unit u)
              (x : assembly_universe_el un)
    : assembly_universe_contains_unit_iso_inv
        un
        (assembly_universe_contains_unit_iso_mor un x)
      =
      x.
  Proof.
    exact (assembly_morphism_eq_point
             (z_iso_inv_after_z_iso (assembly_universe_contains_unit_iso un))
             x).
  Qed.

  (** * 7. Construction of the universe in the comprehension category of assemblies *)
  Section Universe.
    Context (u : assembly_universe).

    Definition assembly_comp_cat_univ
      : dep_assembly (terminal_assembly A)
      := λ _, discrete_assembly A u.

    Definition assembly_comp_cat_el
               (Γ : assembly A)
               (t : comp_cat_tm
                      (C := assembly_comp_cat)
                      (λ (γ : Γ), assembly_comp_cat_univ tt))
      : dep_assembly Γ
      := λ γ, assembly_universe_el (section_to_assembly_term _ t γ).

    Proposition assembly_comp_cat_el_stable_path
                {Γ Δ : assembly A}
                (s : assembly_morphism Γ Δ)
                (t : comp_cat_tm
                       (C := assembly_comp_cat)
                       (λ (γ : Δ), assembly_comp_cat_univ tt))
                (γ : Γ)
      : section_to_assembly_term
          (λ (δ : Δ), assembly_comp_cat_univ tt) t (s γ)
        =
        section_to_assembly_term
          (λ (_ : Γ), assembly_comp_cat_univ tt)
          (comp_cat_subst_tm
             (C := assembly_comp_cat)
             s t
           ↑ ⌈ sub_comp_cat_univ_iso (C := assembly_comp_cat) assembly_comp_cat_univ s ⌉) 
          γ.
    Proof.
      refine (!_).
      etrans.
      {
        refine (maponpaths (λ z, pr1 z _) _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(homotweqinvweq (assembly_term_weq_section _) _)).
          }
          apply coerce_assembly_comp_cat.
        }
        etrans.
        {
          do 3 apply maponpaths.
          apply subst_tm_assembly_comp_cat_alt.
        }
        exact (homotinvweqweq (assembly_term_weq_section _) _).
      }
      refine (fiber_comp_dep_assembly _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply assembly_comp_cat_subst_ty_comp_iso.
      }
      etrans.
      {
        apply assembly_comp_cat_subst_ty_iso.
      }
      use (transportf_set assembly_comp_cat_univ).
      apply setproperty.
    Qed.
    
    Definition assembly_comp_cat_el_stable
               {Γ Δ : assembly A}
               (s : assembly_morphism Γ Δ)
               (t : comp_cat_tm
                      (C := assembly_comp_cat)
                      (λ (γ : Δ), assembly_comp_cat_univ tt))
      : z_iso
          (C := fiber_category_data (disp_cat_of_dep_assembly A) Γ)
          (λ x, assembly_comp_cat_el Δ t (s x))
          (assembly_comp_cat_el
             Γ
             (comp_cat_subst_tm
                (C := assembly_comp_cat)
                s t
              ↑ ⌈ sub_comp_cat_univ_iso (C := assembly_comp_cat) assembly_comp_cat_univ s ⌉)).
    Proof.
      use make_z_iso.
      - use make_dep_assembly_morphism.
        + intros γ x.
          exact (assembly_universe_eq (assembly_comp_cat_el_stable_path s t γ) x).
        + abstract
            (use hinhpr ;
             refine (K* ,, _) ;
             intros γ x a₁ a₂ p q ;
             rewrite combinatory_algebra_ks_eq ;
             apply realizes_assembly_universe_eq ;
             exact q).
      - use make_dep_assembly_morphism.
        + intros γ x.
          exact (assembly_universe_eq (!(assembly_comp_cat_el_stable_path s t γ)) x).
        + abstract
            (use hinhpr ;
             refine (K* ,, _) ;
             intros γ x a₁ a₂ p q ;
             rewrite combinatory_algebra_ks_eq ;
             apply realizes_assembly_universe_eq ;
             exact q).
      - abstract
          (split ;
           use dep_assembly_morphism_eq ;
           intros γ x ;
           refine (fiber_comp_dep_assembly _ _ _ @ _) ;
           refine (!(assembly_universe_eq_comp _ _ _) @ _) ;
           refine (_ @ assembly_universe_eq_idpath _ _) ;
           apply assembly_universe_eq_path).
    Defined.
    
    Definition assembly_comp_cat_universe_data
      : comp_cat_universe_data assembly_comp_cat.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact assembly_comp_cat_univ.
      - exact assembly_comp_cat_el.
      - intros Γ Δ s t.
        exact (assembly_comp_cat_el_stable s t).
    Defined.

    Proposition assembly_comp_cat_el_map_eq_path
                {Γ : assembly A}
                {t₁ t₂ : comp_cat_tm
                           (C := assembly_comp_cat)
                           (λ (γ : Γ), assembly_comp_cat_univ tt)}
                (p : t₁ = t₂)
                (γ : Γ)
      : section_to_assembly_term (λ (γ : Γ), assembly_comp_cat_univ tt) t₁ γ
        =
        section_to_assembly_term (λ (γ : Γ), assembly_comp_cat_univ tt) t₂ γ.
    Proof.
      induction p.
      apply idpath.
    Defined.
      
    Proposition assembly_comp_cat_el_map_eq
                {Γ : assembly A}
                {t₁ t₂ : comp_cat_tm
                           (C := assembly_comp_cat)
                           (λ (γ : Γ), assembly_comp_cat_univ tt)}
                (p : t₁ = t₂)
                {γ : Γ}
                (x : assembly_comp_cat_el Γ t₁ γ)
      : pr1 (CompCatUniverse.el_map assembly_comp_cat_universe_data _ p) γ x
        =
        assembly_universe_eq (assembly_comp_cat_el_map_eq_path p γ) x.
    Proof.
      induction p ; cbn.
      apply idpath.
    Qed.

    Proposition assembly_comp_cat_universe_coherent
      : comp_cat_universe_coherent assembly_comp_cat_universe_data.
    Proof.
      split.
      - intros Γ t.
        use dep_assembly_morphism_eq.
        intros γ x.
        refine (!_).
        refine (fiber_comp_dep_assembly _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply fiber_comp_dep_assembly.
        }
        etrans.
        {
          do 2 apply maponpaths.
          apply assembly_comp_cat_subst_ty_id_iso.
        }
        etrans.
        {
          apply assembly_comp_cat_el_map_eq.
        }
        refine (!(assembly_universe_eq_comp _ _ _) @ _).
        refine (_ @ assembly_universe_eq_idpath _ _).
        apply assembly_universe_eq_path.
      - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
        use dep_assembly_morphism_eq.
        intros γ x.
        refine (fiber_comp_dep_assembly _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply assembly_comp_cat_reindex_iso.
        }
        refine (!_).
        refine (fiber_comp_dep_assembly _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply fiber_comp_dep_assembly.
        }
        etrans.
        {
          do 2 apply maponpaths.
          apply assembly_comp_cat_subst_ty_comp_iso.
        }
        etrans.
        {
          apply assembly_comp_cat_el_map_eq.
        }
        refine (_ @ assembly_universe_eq_comp _ _ _).
        refine (!(assembly_universe_eq_comp _ _ _) @ _).
        apply assembly_universe_eq_path.
    Qed.
  
    Definition assembly_comp_cat_universe
      : comp_cat_universe assembly_comp_cat
      := assembly_comp_cat_universe_data
         ,,
         assembly_comp_cat_universe_coherent.

    Definition assembly_comp_cat_with_universe
      : comp_cat_with_universe
      := assembly_comp_cat ,, assembly_comp_cat_universe.

    (** * 8. The universe contains the unit type *)
    Section ContainsUnit.
      Context (un : assembly_universe_contains_unit u).

      Definition assembly_comp_cat_unit_code
        : assembly_term (λ (_ : terminal_assembly A), assembly_comp_cat_univ tt).
      Proof.
        use make_assembly_term.
        - exact (λ _, un).
        - abstract
            (use hinhpr ;
             refine (I ,, _) ;
             intros ; 
             exact tt).
      Defined.

      Definition assembly_comp_cat_contains_unit_mor
        : dep_assembly_morphism
            (assembly_comp_cat_el
               (terminal_assembly A)
               (assembly_term_to_section
                  _
                  assembly_comp_cat_unit_code))
            (terminal_dep_assembly (terminal_assembly A))
            (id_assembly_morphism _).
      Proof.
        use make_dep_assembly_morphism.
        - refine (λ γ x,
                  assembly_universe_contains_unit_iso_mor
                    un
                    (assembly_universe_eq _ x)).
          exact (maponpaths
                   (λ z, pr1 z γ)
                   (homotinvweqweq
                      (assembly_term_weq_section _)
                      assembly_comp_cat_unit_code)).
        - abstract
            (use hinhpr ;
             refine (I ,, _) ;
             intros ;
             exact tt).
      Defined.

      Definition assembly_comp_cat_contains_unit_inv
        : dep_assembly_morphism
            (terminal_dep_assembly (terminal_assembly A))
            (assembly_comp_cat_el
               (terminal_assembly A)
               (assembly_term_to_section
                  _
                  assembly_comp_cat_unit_code))
            (id_assembly_morphism _).
      Proof.
        use make_dep_assembly_morphism.
        - refine (λ γ x,
                  assembly_universe_eq
                    _
                    (assembly_universe_contains_unit_iso_inv un x)).
          exact (!(maponpaths
                     (λ z, pr1 z γ)
                     (homotinvweqweq
                        (assembly_term_weq_section _)
                        assembly_comp_cat_unit_code))).
        - abstract
            (pose proof (assembly_morphism_tracked
                           (assembly_universe_contains_unit_iso_inv un))
              as p ;
             revert p ;
             use factor_through_squash_hProp ;
             intros (a & p) ;
             use hinhpr ;
             refine (K · a ,, _) ;
             intros γ x b₁ b₂ p₁ p₂ ;
             use realizes_assembly_universe_eq ;
             rewrite combinatory_algebra_k_eq ;
             exact (p b₂ x tt)).
      Defined.

      Definition assembly_comp_cat_contains_unit
        : comp_cat_universe_closed_unit
            assembly_comp_cat_with_universe
            assembly_comp_cat_unit.
      Proof.
        simple refine (_ ,, _).
        - use assembly_term_to_section.
          exact assembly_comp_cat_unit_code.
        - use make_z_iso.
          + exact assembly_comp_cat_contains_unit_mor.
          + exact assembly_comp_cat_contains_unit_inv.
          + abstract
              (split ;
               use dep_assembly_morphism_eq ;
               intros γ x ;
               refine (fiber_comp_dep_assembly _ _ _ @ _) ;
               cbn ;
               [ rewrite assembly_universe_contains_unit_iso_inv_mor ;
                 rewrite <- assembly_universe_eq_comp ;
                 apply assembly_universe_eq_loop
               | rewrite <- assembly_universe_eq_comp ;
                 rewrite assembly_universe_eq_loop ;
                 apply assembly_universe_contains_unit_iso_mor_inv ]).
      Defined.
    End ContainsUnit.

    (** * 9. The strictification of the comprehension category of assemblies *)
    Section Strictification.
      Context (un : assembly_universe_contains_unit u)
              (sig : comp_cat_universe_closed_sigma
                       assembly_comp_cat_with_universe
                       assembly_comp_cat_sigma).
      
      Definition assembly_cwf
        : cwf
        := cwf_from_comp_cat_with_u
             (C := assembly_comp_cat_with_universe)
             assembly_comp_cat_sigma
             sig
             assembly_comp_cat_unit
             (assembly_comp_cat_contains_unit un).

      Let CC : cwf := assembly_cwf.
      
      Definition strictify_assembly_universe_ctx
        : (CC : UU) ≃ u.
      Proof.
        exact (weqfunfromunit _
               ∘ discrete_assembly_term_weq u (terminal_assembly A)
               ∘ invweq (assembly_term_weq_section _))%weq.
      Defined.

      Definition strictify_assembly_universe_ty
                 (Γ : CC)
        : cwf_ty Γ
          ≃
          (assembly_universe_el (strictify_assembly_universe_ctx Γ) → u).
      Proof.
        refine (_
                ∘ discrete_assembly_term_weq
                    u
                    (total_assembly (assembly_comp_cat_el (terminal_assembly A) Γ))
                ∘ invweq (assembly_term_weq_section _))%weq.
        use weqbfun.
        use invweq.
        exact (weqtotal2overunit _).
      Defined.
      
      Definition strictify_assembly_universe_tm
                 (Γ : CC)
                 (X : cwf_ty Γ)
        : cwf_tm X
          ≃
          ∑ (f : ∏ (γ : assembly_universe_el (strictify_assembly_universe_ctx Γ)),
                 assembly_universe_el (strictify_assembly_universe_ty _ X γ)),
          ∃ (a : A),
          ∏ (x : assembly_universe_el (strictify_assembly_universe_ctx Γ))
            (b : A),
          b ⊩ x
          → (a · b) ⊩ f x.
      Proof.
        refine (_ ∘ invweq (assembly_term_weq_section _))%weq.
        use weq_iso.
        - intro t.
          simple refine (_ ,, _).
          + exact (λ γ, t (tt ,, γ)).
          + abstract
              (pose proof (assembly_term_tracker t) as p ;
               revert p ;
               use factor_through_squash_hProp ;
               intros (a & p) ;
               use hinhpr ;
               refine (B · a · (pair · I) ,, _) ;
               intros x b q ;
               cbn ;
               rewrite combinatory_algebra_b_eq ;
               apply p ;
               cbn ;
               refine (tt ,, _) ;
               rewrite combinatory_algebra_pr2_pair ;
               exact q).
        - intro t.
          use make_assembly_term.
          + intro γ.
            induction γ as [ z γ ].
            induction z.
            exact (pr1 t γ).
          + abstract
              (induction t as [ t p ] ;
               revert p ;
               use factor_dep_through_squash ; [ intro ; apply propproperty | ] ;
               intros (a & p) ;
               use hinhpr ;
               refine (B · a · π₂ ,, _) ;
               cbn ; intros b (z & γ) q ;
               induction z ;
               cbn ; cbn in q ;
               rewrite combinatory_algebra_b_eq ;
               apply p ;
               exact (pr2 q)).
        - abstract
            (intro t ;
             use assembly_term_eq ;
             intros (z & γ) ;
             induction z ;
             apply idpath).
        - abstract
            (intro f ;
             use subtypePath ; [ intro ; apply propproperty | ] ;
             use funextsec ;
             intro γ ;
             apply idpath).
      Defined.
    End Strictification.
  End Universe.
End AssemblyCompCat.
