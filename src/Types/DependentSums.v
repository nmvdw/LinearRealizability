(**

 Dependent sums of assemblies

 In this file, we verify that the comprehension category of dependent assemblies has
 strong dependent sums. There are four main interesting parts in this construction.
 - Since the comprehension category of assemblies is full, one can define dependent
   sums as left adjoints of the weakening functor. These left adjoints are constructed
   via reflections.
 - We show substitution along each context morphism has a left adjoint. As a consequence,
   we also get extensional identity types.
 - To check the Beck-Chevalley condition, we first calculate the canonical natural
   transformation. From this description we can directly see that it is an isomorphism. In
   addition, since the category of assemblies has pullbacks, it suffices to verify the
   Beck-Chevalley for the chosen pullbacks.
 - We also need to verify that the dependent sums are strong meaning that the some
   canonical morphism is an isomorphism. This strongness condition means that we can take
   projections and, for identity types, it means that the reflection rule is satisfied.
   The verification of this condition is direct.

 Contents
 1. Construction of dependent sums
 2. Verification of the Beck-Chevalley condition
 3. Strong dependent sums of assemblies

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.

Require Import BeckChevalleyChosen.
Require Import SetFamilies.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

Section DependentAssemblySums.
  Context {A : combinatory_algebra}.

  (** * 1. Construction of dependent sums *)
  Section DependentSums.
    Context {Γ₁ Γ₂ : assembly A}
            (s : assembly_morphism Γ₁ Γ₂).

    Section DepSum.
      Context (X : dep_assembly Γ₁).

      Definition dep_sum_assembly
                 (y : Γ₂)
        : assembly A.
      Proof.
        use make_assembly.
        - exact (dep_sum_set_fam s X y).
        - exact (λ a xyp, π₁ · a ⊩ pr1 xyp ∧ π₂ · a ⊩ pr12 xyp)%ca.
        - abstract
            (intros x xyp ;
             apply propproperty).
        - abstract
            (intros ( x & xx & p ) ;
             simpl in p ;
             pose proof (assembly_realizes_el x) as q ;
             revert q ;
             use factor_through_squash_hProp ;
             intros ( a₁ & Ha₁ ) ;
             pose proof (assembly_realizes_el xx) as q ;
             revert q ;
             use factor_through_squash_hProp ;
             intros ( a₂ & Ha₂ ) ;
             use hinhpr ;
             refine (pair · a₁ · a₂ ,, _)%ca ; simpl ;
             rewrite combinatory_algebra_pr1_pair ;
             rewrite combinatory_algebra_pr2_pair ;
             exact (Ha₁ ,, Ha₂)).
      Defined.
        
      Definition assembly_dependent_sum_unit
        : dep_assembly_morphism
            X
            (dep_assembly_subst s dep_sum_assembly)
            (id_assembly_morphism _).
      Proof.
        use make_dep_assembly_morphism.
        - exact (λ x xx, dep_sum_set_fam_unit s X xx).
        - abstract
            (use hinhpr ;
             refine (pair ,, _) ;
             intros x xx b₁ b₂ p₁ p₂ ; simpl ;
             rewrite combinatory_algebra_pr1_pair ;
             rewrite combinatory_algebra_pr2_pair ;
             exact (p₁ ,, p₂)).
      Defined.
      
      Definition assembly_dependent_sum_type_reflection_data
        : reflection_data
            (D := (disp_cat_of_dep_assembly A)[{Γ₁}])
            X
            (fiber_functor_from_cleaving
               (disp_cat_of_dep_assembly A)
               (dep_assembly_cleaving A)
               s).
      Proof.
        use make_reflection_data.
        - exact dep_sum_assembly.
        - exact assembly_dependent_sum_unit.
      Defined.

      Definition dep_assembly_pr
                 {X' : dep_assembly Γ₂}
                 (f : dep_assembly_morphism
                        X
                        (λ x, X' (s x))
                        (id_assembly_morphism Γ₁))
        : dep_assembly_morphism dep_sum_assembly X' (id_assembly_morphism Γ₂).
      Proof.
        use make_dep_assembly_morphism.
        - exact (λ x xx, dep_sum_set_fam_pr _ X' f xx).
        - abstract
            (pose proof (dep_assembly_morphism_function_track f) as q ;
             revert q ;
             use factor_through_squash_hProp ;
             intros ( a & Ha ) ;
             use hinhpr ;
             refine (dep_π · a ,, _)%ca ;
             intros x xx b₁ b₂ p₁ p₂ ;
             rewrite combinatory_algebra_dep_sum_pr_eq ;
             use dep_assembly_transportf_realizes ;
             exact (Ha _ _ _ _ (pr1 p₂) (pr2 p₂))).
      Defined.
      
      Proposition assembly_dependent_sum_type_reflection_laws
        : is_reflection
            assembly_dependent_sum_type_reflection_data.
      Proof.
        intro f.
        induction f as [ X' f ].
        use make_iscontr.
        - simple refine (_ ,, _).
          + exact (dep_assembly_pr f).
          + abstract
              (use dep_assembly_morphism_eq ;
               intros x xx ;
               refine (_ @ !(transportf_dep_assembly_mor (A := A) _ _ _)) ;
               refine (!_) ;
               etrans ;
               [ apply maponpaths ;
                 apply (transportf_dep_assembly_mor
                          (id_right _ @ !(id_left _))
                          (X₁ := dep_assembly_subst s dep_sum_assembly)
                          (X₂ := X'))
               | ] ;
               cbn ;
               rewrite (functtransportf s X') ;
               rewrite transport_f_f ;
               refine (_ @ idpath_transportf X' _) ;
               apply maponpaths_2 ;
               apply setproperty).
        - abstract
            (intros [ g p ] ; cbn in g, p ;
             use subtypePath ; [ intro ; apply homset_property | ] ;
             use dep_assembly_morphism_eq ;
             intros x xx ; cbn ;
             induction xx as [ x' [ y q ]] ; cbn in q ;
             induction q ; cbn ;
             refine (!_) ;
             etrans ;
             [ refine (dep_assembly_morphism_eq_point p _ @ _) ;
               refine (transportf_dep_assembly_mor (A := A) _ _ _ @ _) ;
               apply maponpaths ;
               apply (transportf_dep_assembly_mor
                        (id_right _ @ !(id_left _))
                        (X₁ := dep_assembly_subst s dep_sum_assembly)
                        (X₂ := X'))
             | ] ;
             cbn ;
             rewrite (functtransportf s X') ;
             rewrite !transport_f_f ;
             refine (_ @ idpath_transportf X' _) ;
             apply maponpaths_2 ;
             apply setproperty).
      Defined.
      
      Definition assembly_dependent_sum_type_reflection
        : reflection
            (D := (disp_cat_of_dep_assembly A)[{Γ₁}])
            X
            (fiber_functor_from_cleaving
               (disp_cat_of_dep_assembly A)
               (dep_assembly_cleaving A)
               s).
      Proof.
        use make_reflection.
        - exact assembly_dependent_sum_type_reflection_data.
        - exact assembly_dependent_sum_type_reflection_laws.
      Defined.
    End DepSum.
    
    Definition assembly_dependent_sum_type
      : dependent_sum (dep_assembly_cleaving A) s.
    Proof.
      use reflections_to_is_right_adjoint.
      exact assembly_dependent_sum_type_reflection.
    Defined.

    Proposition assembly_dependent_sum_on_mor
                {X₁ X₂ : dep_assembly Γ₁}
                (f : dep_assembly_morphism X₁ X₂ (id_assembly_morphism Γ₁))
                {x : Γ₂}
                (xx : dep_sum_assembly X₁ x)
      : pr1 (#(left_adjoint assembly_dependent_sum_type) f) x xx
        =
        make_dep_sum_set_fam
          (dep_sum_set_fam_fib xx)
          (f _ (dep_sum_set_fam_el xx))
          (dep_sum_set_fam_path xx).
    Proof.
      cbn.
      use dep_sum_set_fam_eq.
      - abstract
          (unfold dep_sum_set_fam_fib, dep_sum_set_fam_pr ;
           cbn ;
           rewrite pr1_transportf ;
           rewrite transportf_const ;
           cbn ;
           rewrite (transportf_dep_assembly_mor
                      (id_right _)
                      (comp_dep_assembly_morphism f (assembly_dependent_sum_unit X₂))) ;
           cbn ;
           rewrite pr1_transportf ;
           rewrite transportf_const ;
           apply idpath).
      - induction xx as [ y [ yy p ]].
        cbn in *.
        induction p ; cbn.
        etrans.
        {
          apply maponpaths.
          use dep_sum_set_fam_el_eq.
          {
            exact (make_dep_sum_set_fam y (f y yy) (idpath _)).
          }
          etrans.
          {
            apply (transportf_dep_assembly_mor
                     (id_right _)
                     (comp_dep_assembly_morphism f (assembly_dependent_sum_unit X₂))).
          }
          cbn.
          rewrite transportf_set.
          {
            apply idpath.
          }
          apply setproperty.
        }
        cbn.
        rewrite transport_f_f.
        rewrite transportf_set.
        {
          apply idpath.
        }
        apply setproperty.
    Qed.

    Proposition assembly_dependent_sum_counit
                {X : dep_assembly Γ₂}
                {x : Γ₂}
                (xx : dep_sum_assembly (dep_assembly_subst s X) x)
      : pr1 (counit_from_right_adjoint assembly_dependent_sum_type X) x xx
        =
        transportf X (dep_sum_set_fam_path xx) (dep_sum_set_fam_el xx).
    Proof.
      apply idpath.
    Qed.
  End DependentSums.

  (** * 2. Verification of the Beck-Chevalley condition *)
  Section BeckChevalley.
    Context {Γ₁ Γ₂ Γ₃ : assembly A}
            {f₁ : assembly_morphism Γ₂ Γ₁}
            {f₂ : assembly_morphism Γ₃ Γ₁}
            (X : dep_assembly Γ₂).

    Let Γ₄ : assembly A := pullback_assembly f₁ f₂.
    Let p₁ : assembly_morphism Γ₄ Γ₂ := pullback_assembly_pr1 f₁ f₂.
    Let p₂ : assembly_morphism Γ₄ Γ₃ := pullback_assembly_pr2 f₁ f₂.
    Let e : comp_assembly_morphism p₁ f₁ = comp_assembly_morphism p₂ f₂
      := PullbackSqrCommutes (pullbacks_cat_of_assembly A Γ₁ Γ₂ Γ₃ f₁ f₂).

    Proposition left_beck_chevalley_nat_trans_dep_assembly_path
                {x : Γ₃}
                (xx : dep_sum_set_fam p₂ (λ (x : pullback_assembly f₁ f₂), X (p₁ x)) x)
      : f₁ (pr1 (dep_sum_set_fam_fib xx)) = f₂ x.
    Proof.
      refine (_ @ maponpaths f₂ (pr22 xx)).      
      exact (assembly_morphism_eq_point e (pr1 xx)).
    Qed.
    
    Proposition left_beck_chevalley_nat_trans_dep_assembly
                {x : Γ₃}
                (xx : dep_sum_set_fam p₂ (λ (x : pullback_assembly f₁ f₂), X (p₁ x)) x)
      : pr1 (left_beck_chevalley_nat_trans
               (assembly_dependent_sum_type f₁)
               (assembly_dependent_sum_type p₂)
               (comm_nat_z_iso (dep_assembly_cleaving A) f₁ f₂ p₂ p₁ e)
               X)
          x
          xx
        =
        make_dep_sum_set_fam
          (p₁ (dep_sum_set_fam_fib xx))
          (dep_sum_set_fam_el xx)
          (left_beck_chevalley_nat_trans_dep_assembly_path xx).
    Proof.
      pose (left_beck_chevalley_nat_trans_ob
              (assembly_dependent_sum_type f₁)
              (assembly_dependent_sum_type p₂)
              (comm_nat_z_iso (dep_assembly_cleaving A) f₁ f₂ p₂ p₁ e)
              X)
        as q.
      rewrite q.
      clear q.
      etrans.
      {
        refine (fiber_comp_dep_assembly _ _ _ @ _).
        apply maponpaths.
        apply fiber_comp_dep_assembly.
      }
      etrans.
      {
        do 2 apply maponpaths.
        exact (assembly_dependent_sum_on_mor _ _ _).
      }
      etrans.
      {
        apply maponpaths.
        exact (assembly_dependent_sum_on_mor _ _ _).
      }
      etrans.
      {
        apply assembly_dependent_sum_counit.
      }
      etrans.
      {
        cbn -[fiber_functor_from_cleaving comm_nat_z_iso].
        apply maponpaths.
        exact (comm_nat_z_iso_dep_assembly _ _).
      }
      etrans.
      {
        do 2 apply maponpaths.
        exact (fiber_functor_from_cleaving_dep_assembly _ _ _).
      }
      cbn.
      use dep_sum_set_fam_eq.
      - abstract
          (unfold dep_sum_set_fam_fib ;
           cbn ;
           rewrite !pr1_transportf ;
           rewrite !transportf_const ;
           cbn ;
           apply idpath).
      - unfold dep_sum_set_fam_path.
        induction xx as [ y [ xx p ]].
        cbn in *.
        induction p.
        cbn.
        etrans.
        {
          apply maponpaths.
          use dep_sum_set_fam_el_transportf.
        }
        rewrite transport_f_f.
        cbn.
        rewrite transportf_set.
        {
          apply idpath.
        }
        apply setproperty.        
    Qed.

    Definition dep_assembly_sum_bc_isomorphism
      : dep_assembly_morphism
          (dep_sum_assembly p₂ (dep_assembly_subst p₁ X))
          (dep_assembly_subst f₂ (dep_sum_assembly f₁ X))
          (id_assembly_morphism Γ₃).
    Proof.
      use make_dep_assembly_morphism.
      - refine (λ x xyp, make_dep_sum_set_fam _ _ _).
        + exact (dep_sum_set_fam_el xyp).
        + apply left_beck_chevalley_nat_trans_dep_assembly_path.
      - abstract
          (use hinhpr ;
           simple refine (sum_s ,, _) ;
           intros x xx b₁ b₂ q₁ q₂ ;
           simpl ;
           rewrite combinatory_algebra_dep_sum_stable_eq ;
           rewrite combinatory_algebra_pr1_pair ;
           rewrite combinatory_algebra_pr2_pair ;
           simpl in q₂ ;
           exact (pr11 q₂ ,, pr2 q₂)).
    Defined.

    Definition dep_assembly_sum_bc_isomorphism_inv
      : dep_assembly_morphism
          (dep_assembly_subst f₂ (dep_sum_assembly f₁ X))
          (dep_sum_assembly p₂ (dep_assembly_subst p₁ X))
          (id_assembly_morphism Γ₃).
    Proof.
      use make_dep_assembly_morphism.
      - refine (λ x xyp, _).
        use make_dep_sum_set_fam.
        + simple refine (_ ,, _ ,, _).
          * exact (dep_sum_set_fam_fib xyp).
          * exact x.
          * exact (dep_sum_set_fam_path xyp).
        + exact (dep_sum_set_fam_el xyp).
        + apply idpath.
      - abstract
          (use hinhpr ;
           simple refine (sum_si ,, _) ;
           intros x xx b₁ b₂ q₁ q₂ ;
           simpl ;
           rewrite combinatory_algebra_dep_sum_stable_inv_eq ;
           rewrite !combinatory_algebra_pr1_pair ;
           rewrite !combinatory_algebra_pr2_pair ;
           simpl in q₂ ;
           unfold dep_sum_set_fam_el ;
           refine ((pr1 q₂ ,, q₁) ,, pr2 q₂)).
    Defined.

    Proposition is_z_isomorphism_dep_assembly_sum_bc_isomorphism_invs
      : is_inverse_in_precat
          (C := (disp_cat_of_dep_assembly A)[{_}])
          dep_assembly_sum_bc_isomorphism
          dep_assembly_sum_bc_isomorphism_inv.
    Proof.
      split.
      - use dep_assembly_morphism_eq.
        intros x xx.
        refine (fiber_comp_dep_assembly _ _ _ @ _).
        induction xx as [ y [ yy p ]].
        induction y as [ y₁ [ y₂ q ]].
        cbn in p.
        induction p.
        use dep_sum_set_fam_eq.
        + cbn.
          do 2 apply maponpaths.
          apply setproperty.
        + cbn.
          rewrite (functtransportf pr1 X).
          rewrite transportf_set.
          {
            apply idpath.
          }
          apply setproperty.
      - use dep_assembly_morphism_eq.
        intros x xx.
        refine (fiber_comp_dep_assembly _ _ _ @ _).
        cbn.
        induction xx as [ y [ yy p ]].
        cbn in *.
        do 2 apply maponpaths.
        apply setproperty.
    Qed.
    
    Definition is_z_isomorphism_dep_assembly_sum_bc_isomorphism
      : is_z_isomorphism
          (C := (disp_cat_of_dep_assembly A)[{Γ₃}])
          dep_assembly_sum_bc_isomorphism.
    Proof.
      use make_is_z_isomorphism.
      - exact dep_assembly_sum_bc_isomorphism_inv.
      - exact is_z_isomorphism_dep_assembly_sum_bc_isomorphism_invs.
    Defined.

    Definition is_z_iso_left_beck_chevalley_nat_trans_dep_assembly
      : is_z_isomorphism
          (left_beck_chevalley_nat_trans
             (assembly_dependent_sum_type f₁)
             (assembly_dependent_sum_type p₂)
             (comm_nat_z_iso (dep_assembly_cleaving A) f₁ f₂ p₂ p₁ e)
             X).
    Proof.
      use is_z_isomorphism_path.
      - exact dep_assembly_sum_bc_isomorphism.
      - abstract
          (use dep_assembly_morphism_eq ;
           intros y yy ;
           refine (!_) ;
           apply (left_beck_chevalley_nat_trans_dep_assembly yy)).
      - exact is_z_isomorphism_dep_assembly_sum_bc_isomorphism.
    Defined.
  End BeckChevalley.

  (** * 3. Strong dependent sums of assemblies *)
  Definition dep_assembly_dependent_sums
    : has_dependent_sums (dep_assembly_cleaving A).
  Proof.
    use has_dependent_sums_chosen_to_dependent_sum.
    - exact (pullbacks_cat_of_assembly A).
    - use make_has_dependent_sums_chosen.
      + exact (λ _ _ s, assembly_dependent_sum_type s).
      + cbn.
        intros Γ₁ Γ₂ Γ₃ f₁ f₂ X.
        apply is_z_iso_left_beck_chevalley_nat_trans_dep_assembly.
  Defined.

  Definition dep_assembly_dependent_sums_strong_inv
             {Γ₁ Γ₂ : assembly A}
             (s : assembly_morphism Γ₁ Γ₂)
             (X : dep_assembly Γ₁)
    : assembly_morphism
        (total_assembly (dep_sum_assembly s X))
        (total_assembly X).
  Proof.
    use make_assembly_morphism.
    - exact (λ xyp, pr12 xyp ,, pr122 xyp).
    - abstract
        (use hinhpr ;
         refine (sum_str ,, _) ;
         intros a x p ;
         simpl ;
         rewrite combinatory_algebra_dep_sum_stable_strong_eq ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         simpl in p ;
         exact (pr12 p ,, pr22 p)).
  Defined.
  
  Definition dep_assembly_dependent_sums_strong
             {Γ₁ Γ₂ : assembly A}
             (s : assembly_morphism Γ₁ Γ₂)
             (X : dep_assembly Γ₁)
    : is_z_isomorphism
        (C := cat_of_assembly A)
        (comp_assembly_morphism
           (total_assembly_morphism (assembly_dependent_sum_unit s X))
           (total_assembly_morphism (dep_assembly_subst_mor s (dep_sum_assembly s X)))).
  Proof.
    use make_is_z_isomorphism.
    - exact (dep_assembly_dependent_sums_strong_inv s X).
    - abstract
        (split ; use assembly_morphism_eq ; intro x ; cbn ; [ apply idpath | ] ;
         induction x as [ y [ x [ xx p ] ] ] ;
         cbn in * ;
         induction p ;
         apply idpath).
  Defined.
End DependentAssemblySums.
