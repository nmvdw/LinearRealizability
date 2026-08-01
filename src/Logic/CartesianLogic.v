(**

 Logic in realizability model (Cartesian case)

 In this file, we construct a tripos whose formulas are terms of type `Prop` in the
 realizability model. The necessary connectives are defined in another file, and here
 we show that the necessary rules are satisfied. We restrict ourselves to the Cartesian
 case in this file.

 Content
 1. The hyperdoctrine of propositions of assemblies
 2. Fiberwise terminal object
 3. Fiberwise initial object
 4. Fiberwise binary products
 5. Fiberwise binary coproducts
 6. Fiberwise exponentials
 7. The Cartesian monoidal structure
 8. The universal quantifier
 9. The existential quantifier
 10. Equality
 11. The first-order hyperdoctrine
 12. Extensionality
 13. It is a tripos
 14. The comprehension functor

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrineChosen.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Basics.BIAlgebra.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Types.Terms.
Require Import Types.Prop.
Require Import Logic.Formulas.
Require Import Logic.Connectives.

Local Open Scope ca.
Local Open Scope assembly.

Section CartesianLogic.
  Context (A : combinatory_algebra).

  (** * 1. The hyperdoctrine of propositions of assemblies *)
  Definition assembly_prop_preorder_hyperdoctrine
    : preorder_hyperdoctrine.
  Proof.
    use make_preorder_hyperdoctrine.
    - exact (cat_of_assembly A).
    - exact (assembly_prop_disp_cat A).
    - exact (terminal_cat_of_assembly A).
    - exact (binproducts_cat_of_assembly A).
    - exact (cleaving_assembly_prop_disp_cat A).
    - apply locally_propositional_assembly_prop_disp_cat.
  Defined.

  (** * 2. Fiberwise terminal object *)
  Definition fiberwise_terminal_assembly_prop_disp_cat
    : fiberwise_terminal (cleaving_assembly_prop_disp_cat A).
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - apply locally_propositional_assembly_prop_disp_cat.
    - exact assembly_truth_prop.
    - abstract
        (intros Γ φ ;
         use (make_assembly_prop_proof I) ;
         intros ; cbn ;
         exact tt).
    - abstract
        (intros Γ₁ Γ₂ s ;
         use (make_assembly_prop_proof I) ; cbn ;
         intros ;
         exact tt).
  Defined.      

  (** * 3. Fiberwise initial object *)
  Definition fiberwise_initial_assembly_prop_disp_cat
    : fiberwise_initial (cleaving_assembly_prop_disp_cat A).
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - apply locally_propositional_assembly_prop_disp_cat.
    - exact assembly_false_prop.
    - abstract
        (intros Γ φ ;
         use (make_assembly_prop_proof I) ; cbn ;
         intros x b₁ b₂ q xx ;
         induction xx).
    - abstract
        (intros Γ₁ Γ₂ s ;
         use (make_assembly_prop_proof I) ; cbn ;
         intros x b₁ b₂ q xx ;
         induction xx).
  Defined.

  (** * 4. Fiberwise binary products *)
  Definition fiberwise_binproducts_assembly_prop_disp_cat
    : fiberwise_binproducts (cleaving_assembly_prop_disp_cat A).
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - apply locally_propositional_assembly_prop_disp_cat.
    - exact (λ Γ t₁ t₂, assembly_conj_prop t₁ t₂).
    - abstract
        (intros Γ t₁ t₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_K_pr1 _)) ;
         cbn -[combinatory_algebra_K_pr1] ;
         intros x b₁ b₂ q₁ q₂ ;
         rewrite combinatory_algebra_K_pr1_eq ;
         exact (pr1 q₂)).
    - abstract
        (intros Γ t₁ t₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_K_pr2 _)) ;
         cbn -[combinatory_algebra_K_pr2] ;
         intros x b₁ b₂ q₁ q₂ ;
         rewrite combinatory_algebra_K_pr2_eq ;
         exact (pr2 q₂)).
    - abstract
        (intros Γ t₁ t₂ u p₁ p₂ ;
         pose proof (assembly_prop_to_proof p₁) as q₁ ;
         revert q₁ ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_prop_disp_cat | ] ;
         intros ( a₁ & q₁ ) ;
         pose proof (assembly_prop_to_proof p₂) as q₂ ;
         revert q₂ ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_prop_disp_cat | ] ;
         intros ( a₂ & q₂ ) ;
         clear p₁ p₂ ;
         use (make_assembly_prop_proof (pairf2 · a₁ · a₂)) ;
         intros x b₁ b₂ r₁ r₂ ;
         simpl ;
         rewrite combinatory_algebra_pr1_pair_fun_two ;
         rewrite combinatory_algebra_pr2_pair_fun_two ;
         specialize (q₁ x b₁ b₂ r₁ r₂) ;
         specialize (q₂ x b₁ b₂ r₁ r₂) ;
         exact (q₁ ,, q₂)).
    - abstract
        (intros Γ₁ Γ₂ s t₁ t₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_ks _)) ; cbn ;
         intros x b₁ b₂ q₁ q₂ ;
         rewrite !combinatory_algebra_ks_eq ;
         exact q₂).
  Defined.

  (** * 5. Fiberwise binary coproducts *)
  Definition fiberwise_bincoproducts_assembly_prop_disp_cat
    : fiberwise_bincoproducts (cleaving_assembly_prop_disp_cat A).
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - apply locally_propositional_assembly_prop_disp_cat.
    - exact (λ Γ t₁ t₂, assembly_disj_prop t₁ t₂).
    - abstract
        (intros Γ t₁ t₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_disj_inl _)) ;
         intros x b₁ b₂ q₁ q₂ ;
         use hdisj_in1 ;
         cbn -[combinatory_algebra_disj_inl] ;
         rewrite combinatory_algebra_disj_inl_eq ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         exact (idpath _ ,, q₂)).
    - abstract
        (intros Γ t₁ t₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_disj_inr _)) ;
         intros x b₁ b₂ q₁ q₂ ;
         use hdisj_in2 ;
         cbn -[combinatory_algebra_disj_inr] ;
         rewrite combinatory_algebra_disj_inr_eq ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         exact (idpath _ ,, q₂)).
    - abstract
        (intros Γ t₁ t₃ u p₁ p₂ ;
         pose proof (assembly_prop_to_proof p₁) as q₁ ;
         revert q₁ ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_prop_disp_cat | ] ;
         intros ( a₁ & q₁ ) ;
         clear p₁ ;
         pose proof (assembly_prop_to_proof p₂) as q₂ ;
         revert q₂ ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_prop_disp_cat | ] ;
         intros ( a₂ & q₂ ) ;
         clear p₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_disj_elim _ · a₁ · a₂)) ;
         intros x b₁ b₂ r₁ ;
         use factor_through_squash_hProp ;
         rewrite combinatory_algebra_disj_elim_eq ;
         intros r₂ ;
         induction r₂ as [[ r₂ r₃ ] | [ r₂ r₃ ]] ;
         [ rewrite <- r₂ ;
           rewrite combinatory_algebra_k_eq ;
           exact  (q₁ _ _ _ r₁ r₃)
         | rewrite <- r₂ ;
           rewrite combinatory_algebra_ks_eq ;
           exact  (q₂ _ _ _ r₁ r₃) ]).
    - abstract
        (intros Γ₁ Γ₂ s t₁ t₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_disj_subst _)) ;
         intros x b₁ b₂ q₁ ;
         use factor_through_squash_hProp ;
         intros q₂ ;
         induction q₂ as [ [ q₂ q₃ ] | [ q₂ q₃ ]] ;
         [ use hdisj_in1 | use hdisj_in2 ] ;
         cbn -[combinatory_algebra_disj_subst] ;
         rewrite combinatory_algebra_disj_subst_eq ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         exact (q₂ ,, q₃)).
  Defined.

  (** * 6. Fiberwise exponentials *)
  Definition fiberwise_exponentials_assembly_prop_disp_cat
    : fiberwise_exponentials fiberwise_binproducts_assembly_prop_disp_cat.
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - apply locally_propositional_assembly_prop_disp_cat.
    - cbn.
      exact (λ Γ t₁ t₂, assembly_impl_prop t₁ t₂).
    - abstract
        (cbn ;
         intros Γ t₁ t₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_impl_intro _)) ;
         cbn -[combinatory_algebra_impl_intro] ;
         intros x b₁ b₂ q₁ (q₂ & q₃) ;
         rewrite combinatory_algebra_impl_intro_eq ;
         exact (q₃ _ q₂)).
    - abstract
        (cbn ;
         intros Γ t₁ t₂ t₃ p ;
         pose proof (assembly_prop_to_proof p) as q ;
         revert q ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_prop_disp_cat | ] ;
         intros ( a & r ) ;
         clear p ;
         use (make_assembly_prop_proof (combinatory_algebra_impl_elim _ · a)) ;
         intros x b₁ b₂ q₁ q₂ b₃ q₃ ;
         rewrite combinatory_algebra_impl_elim_eq ;
         specialize (r _ _ (pair · b₃ · b₂) q₁) ;
         cbn in r ;
         rewrite combinatory_algebra_pr1_pair in r ;
         rewrite combinatory_algebra_pr2_pair in r ;
         exact (r (q₃ ,, q₂))).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ s t₁ t₂ ;
         use (make_assembly_prop_proof (combinatory_algebra_all_subst _)) ;
         cbn -[combinatory_algebra_all_subst] ;
         intros x b₁ b₂ q₁ q₂ b₃ q₃ ;
         rewrite combinatory_algebra_all_subst_eq ;
         exact (q₂ _ q₃)).
  Defined.

  (** * 7. The Cartesian monoidal structure *)
  Definition assembly_prop_cartesian_monoidalcat
             (Γ : assembly A)
    : monoidal_cat
    := cartesian_monoidalcat
         _
         (pr1 fiberwise_binproducts_assembly_prop_disp_cat Γ)
         (terminal_in_fib fiberwise_terminal_assembly_prop_disp_cat Γ).

  Definition assembly_prop_cartesian_monoidalcat_symmetric
             (Γ : assembly A)
    : symmetric (assembly_prop_cartesian_monoidalcat Γ)
    := symmetric_cartesian_monoidalcat _ _ _.

  Definition assembly_prop_sym_monoidal_cat
             (Γ : assembly A)
    : sym_monoidal_cat
    := assembly_prop_cartesian_monoidalcat Γ
       ,,
       assembly_prop_cartesian_monoidalcat_symmetric Γ.

  (** * 8. The universal quantifier *)
  Definition assembly_prop_universal_quantifiers
    : universal_quantifiers assembly_prop_preorder_hyperdoctrine.
  Proof.
    use universal_quantifiers_from_chosen.
    use make_universal_quantifiers_chosen.
    - cbn.
      exact (λ Γ X t, assembly_forall_prop t).
    - abstract
        (cbn ;
         intros Γ X t ;
         use (make_assembly_prop_proof (combinatory_algebra_all_intro _)) ;
         intros (x & y) b₁ b₂ (q₁ & q₂) q₃ ;
         rewrite combinatory_algebra_all_intro_eq ;
         cbn in *  ;
         exact (q₃ y (π₂ · b₁) q₂)).
    - abstract
        (cbn ;
         intros Γ X t₁ t₂ p ;
         pose proof (assembly_prop_to_proof p) as q ;
         revert q ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_prop_disp_cat | ] ;
         intros ( a & r ) ;
         clear p ;
         cbn in r ;
         use (make_assembly_prop_proof (combinatory_algebra_all_elim _ · a)) ;
         intros x b₁ b₂ q₁ q₂ y b₃ q₃ ;
         rewrite combinatory_algebra_all_elim_eq ;
         specialize (r (x ,, y) (pair · b₁ · b₃) b₂) ;
         cbn in r ;
         rewrite combinatory_algebra_pr1_pair in r ;
         rewrite combinatory_algebra_pr2_pair in r ;
         exact (r (q₁ ,, q₃) q₂)).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ X s t ;
         use (make_assembly_prop_proof (combinatory_algebra_all_subst _)) ;
         cbn -[combinatory_algebra_all_subst] ;
         intros x b₁ b₂ q₁ q₂ y b₃ q₃ ;
         rewrite combinatory_algebra_all_subst_eq ;
         exact (q₂ y b₃ q₃)).
  Defined.

  (** * 9. The existential quantifier *)
  Definition assembly_prop_existential_quantifiers
    : existential_quantifiers assembly_prop_preorder_hyperdoctrine.
  Proof.
    use existential_quantifiers_from_chosen.
    use make_existential_quantifiers_chosen.
    - cbn.
      exact (λ Γ X t, assembly_exists_prop t).
    - abstract
        (cbn ;
         intros Γ X t ;
         use (make_assembly_prop_proof
                (combinatory_algebra_fun_pair _ · pair · π₂ · I)) ;
         intros (x & y) b₁ b₂ (q₁ & q₂) r ;
         cbn in q₁, q₂ ;
         use hinhpr ; cbn -[combinatory_algebra_fun_pair] ;
         refine (y ,, _) ;
         rewrite combinatory_algebra_fun_pair_eq ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         rewrite combinatory_algebra_i_eq ;
         exact (q₂ ,, r)).
    - abstract
        (cbn ;
         intros Γ X t₁ t₂ p ;
         pose proof (assembly_prop_to_proof p) as q ;
         revert q ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_prop_disp_cat | ] ;
         intros ( a & q ) ;
         cbn in q ;
         clear p ;
         use (make_assembly_prop_proof (combinatory_algebra_ex_elim _ · a)) ;
         intros x b₁ b₂ r ;
         use factor_through_squash_hProp ;
         intros (y & p₁ & p₂) ;
         rewrite combinatory_algebra_ex_elim_eq ;
         refine (q (x ,, y) _ _ _ p₂) ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         cbn ;
         exact (r ,, p₁)).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ X s t ;
         use (make_assembly_prop_proof (combinatory_algebra_ex_subst _)) ;
         intros x b₁ b₂ q₁ ;
         use factor_through_squash_hProp ;
         intros (y & q₂ & q₃) ;
         use hinhpr ;
         cbn -[combinatory_algebra_ex_subst] ;
         refine (y ,, _) ;
         rewrite combinatory_algebra_ex_subst_eq ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         exact (q₂ ,, q₃)).
  Defined.

  (** * 10. Equality *)
  Definition assembly_prop_equality_formulas
    : equality_formulas assembly_prop_preorder_hyperdoctrine.
  Proof.
    use make_equality_formulas.
    - cbn.
      exact (λ Γ t, assembly_equality_prop t).
    - abstract
        (cbn ;
         intros Γ t ;
         use (make_assembly_prop_proof (combinatory_algebra_ks _)) ;
         intros x b₁ b₂ q₁ q₂ ; cbn ;
         refine (idpath _ ,, _) ;
         rewrite combinatory_algebra_ks_eq ;
         exact q₂).
    - abstract
        (cbn ;
         intros Γ t₁ t₂ p ;
         pose proof (assembly_prop_to_proof p) as q ;
         revert q ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_prop_disp_cat | ] ;
         intros ( a & q ) ;
         cbn in q ;
         use (make_assembly_prop_proof (combinatory_algebra_fun_pair _ · a · π₁ · I)) ;
         cbn -[combinatory_algebra_fun_pair] ;
         intros ( x & y ) b₁ b₂ ( q₁ & q₂ ) ( r₁ & r₂ ) ;
         rewrite combinatory_algebra_fun_pair_eq ;
         rewrite combinatory_algebra_i_eq ;
         cbn in * ;
         induction r₁ ;
         exact (q x (π₁ · b₁) b₂ q₁ r₂)).
  Defined.

  (** * 11. The first-order hyperdoctrine *)
  Definition assembly_prop_first_order_preorder_hyperdoctrine
    : first_order_preorder_hyperdoctrine.
  Proof.
    use make_first_order_preorder_hyperdoctrine.
    - exact assembly_prop_preorder_hyperdoctrine.
    - exact fiberwise_terminal_assembly_prop_disp_cat.
    - exact fiberwise_initial_assembly_prop_disp_cat.
    - exact fiberwise_binproducts_assembly_prop_disp_cat.
    - exact fiberwise_bincoproducts_assembly_prop_disp_cat.
    - exact fiberwise_exponentials_assembly_prop_disp_cat.
    - exact assembly_prop_universal_quantifiers.
    - exact assembly_prop_existential_quantifiers.
    - exact assembly_prop_equality_formulas.
  Defined.

  (** * 12. Extensionality *)
  Proposition assembly_prop_extensional
              {Γ X : assembly A}
              {f g : assembly_morphism Γ X}
              (p : dep_assembly_morphism
                     (assembly_prop_universe_el
                        (assembly_truth_prop Γ))
                     (assembly_prop_universe_el
                        (subst_assembly_term
                           (pair_assembly_morphism f g)
                           (assembly_equality_prop (assembly_truth_prop X))))
                     (id_assembly_morphism _))
    : f = g.
  Proof.
    pose proof (assembly_prop_to_proof p) as q.
    revert q.
    use factor_through_squash.
    {
      apply isaset_assembly_morphism.
    }
    intros (a & q).
    cbn in q.
    use assembly_morphism_eq.
    intro x.
    pose proof (assembly_realizes_el x) as r.
    revert r.
    use factor_through_squash.
    {
      apply setproperty.
    }
    intros (b & r).
    exact (pr1 (q x b b r tt)).
  Qed.

  (** * 13. It is a tripos *)
  Definition assembly_prop_comprehension
             {Γ X : assembly A}
             (t : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : assembly_morphism
        X
        (function_assembly
           Γ
           (discrete_assembly A (funset A hPropset)))
    := lam_assembly_morphism t.

  Definition assembly_prop_preorder_tripos
    : preorder_tripos.
  Proof.
    refine (assembly_prop_first_order_preorder_hyperdoctrine ,, _).
    refine (λ Γ, _).
    refine (function_assembly Γ (discrete_assembly A (funset A hPropset)) ,, _).
    refine (assembly_in_prop Γ ,, _).
    intros X t.
    refine (assembly_prop_comprehension t ,, _).
    abstract
      (use assembly_term_eq ;
       intro x ;
       cbn ;
       apply idpath).
  Defined.

  (** * 14. The comprehension functor *)
  Definition assembly_prop_comprehension_functor_ob
             {Γ : cat_of_assembly A}
             (t : assembly_term (assembly_prop_universe_type Γ))
    : disp_mono_codomain (cat_of_assembly A) Γ.
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact (total_assembly (assembly_prop_universe_el t)).
    - exact (total_assembly_pr (assembly_prop_universe_el t)).
    - abstract
        (cbn ; intros Δ f₁ f₂ p ;
         use assembly_morphism_eq ;
         intro x ;
         use (total2_paths_f (assembly_morphism_eq_point p x)) ;
         apply propproperty).
  Defined.

  Definition assembly_prop_comprehension_functor_mor
             {Γ₁ Γ₂ : assembly A}
             {t₁ : assembly_term (assembly_prop_universe_type Γ₁)}
             {t₂ : assembly_term (assembly_prop_universe_type Γ₂)}
             {s : assembly_morphism Γ₁ Γ₂}
             (p : dep_assembly_morphism
                    (assembly_prop_universe_el t₁)
                    (assembly_prop_universe_el t₂)
                    s)
    : assembly_morphism
        (total_assembly (assembly_prop_universe_el t₁))
        (total_assembly (assembly_prop_universe_el t₂)).
  Proof.
    use make_assembly_morphism.
    - intros xq.
      refine (s (pr1 xq) ,, _).
      abstract
        (induction xq as [ x q ] ;
         cbn -[assembly_prop_universe_el] ;
         exact (p x q)).
    - abstract
        (pose proof (assembly_morphism_tracked s) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros (a & q) ;
         pose proof (dep_assembly_morphism_function_track p) as r ;
         revert r ;
         use factor_through_squash_hProp ;
         intros (b & r) ;
         use hinhpr ;
         refine (combinatory_algebra_comprehension _ · a · b ,, _) ;
         intros c x r' ;
         cbn -[combinatory_algebra_comprehension] ;
         rewrite combinatory_algebra_comprehension_eq ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         specialize (q _ _ (pr1 r')) ;
         specialize (r (pr1 x) (pr2 x) _ _ (pr1 r') (pr2 r')) ;
         exact (q ,, r)).
  Defined.
  
  Definition assembly_prop_comprehension_functor_data
    : disp_functor_data
        (functor_identity _)
        (assembly_prop_disp_cat A)
        (disp_mono_codomain (cat_of_assembly A)).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ t, assembly_prop_comprehension_functor_ob t).
    - cbn ; intros Γ₁ Γ₂ t₁ t₂ s p.
      simple refine ((_ ,, _) ,, tt).
      + exact (assembly_prop_comprehension_functor_mor p).
      + abstract
          (use assembly_morphism_eq ;
           intro x ; cbn ;
           apply idpath).
  Defined.
  
  Definition assembly_prop_comprehension_functor
    : disp_functor
        (functor_identity _)
        (assembly_prop_disp_cat A)
        (disp_mono_codomain (cat_of_assembly A)).
  Proof.
    simple refine (_ ,, _).
    - exact assembly_prop_comprehension_functor_data.
    - abstract
        (split ; intros ; apply locally_propositional_mono_cod_disp_cat).
  Defined.

  Proposition assembly_prop_comprehension_in
              {Γ : assembly A}
              (t : assembly_term (assembly_prop_universe_type Γ))
    : dep_assembly_morphism
        (assembly_prop_universe_el
           (assembly_truth_prop _))
        (assembly_prop_universe_el
           (subst_assembly_term
              (MonicArrow _ (mono_cod_mor (assembly_prop_comprehension_functor Γ t)))
              t))
        (id_assembly_morphism _).
  Proof.
    use (make_assembly_prop_proof (Λ (Co K* • V 1 • (Co π₂ • V 0)))).
    intros (x & p) a₁ a₂ (q₁ & q₂) _.
    simpl in q₁, q₂ ; simpl.
    refine (transportb (λ z, (t x z : hProp)) _ q₂).
    etrans.
    {
      apply maponpaths_2.
      apply lam_term_multiple.
    }
    rewrite lam_term_single.
    cbn.
    rewrite combinatory_algebra_ks_eq.
    apply idpath.
  Qed.
  
  Definition make_assembly_prop_comprehension_term
             {Γ X : assembly A}
             (t : assembly_term (assembly_prop_universe_type X))
             (f : assembly_morphism Γ X)
             (p : dep_assembly_morphism
                    (assembly_prop_universe_el
                       (assembly_truth_prop _))
                    (assembly_prop_universe_el
                       (subst_assembly_term f t))
                    (id_assembly_morphism _))
    : assembly_morphism
        Γ
        (mono_cod_dom (assembly_prop_comprehension_functor X t)).
  Proof.
    use make_assembly_morphism.
    - refine (λ x, f x ,, _).
      exact (p x (hinhpr (I ,, tt))).
    - abstract
        (pose proof (assembly_morphism_tracked f) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros (a & q) ;
         pose proof (dep_assembly_morphism_function_track p) as r ;
         revert r ;
         use factor_through_squash_hProp ;
         intros (b & r) ;
         use hinhpr ;
         refine (combinatory_algebra_comprehension_term _ · a · b ,, _) ;
         intros c x s ;
         cbn -[combinatory_algebra_comprehension_term] ;
         rewrite combinatory_algebra_comprehension_term_eq ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         refine (q c x s ,, _) ;
         exact (r x  (hinhpr (I ,, tt)) c a s tt)).
  Defined.

  Proposition make_assembly_prop_comprehension_term_comm
              {Γ X : assembly A}
              (t : assembly_term (assembly_prop_universe_type X))
              (f : assembly_morphism Γ X)
              (p : dep_assembly_morphism
                     (assembly_prop_universe_el
                        (assembly_truth_prop _))
                     (assembly_prop_universe_el
                        (subst_assembly_term f t))
                     (id_assembly_morphism _))
    : comp_assembly_morphism
        (make_assembly_prop_comprehension_term t f p)
        (MonicArrow _ (mono_cod_mor (assembly_prop_comprehension_functor X t)))
      =
      f.
  Proof.
    use assembly_morphism_eq.
    intros x ; cbn.
    apply idpath.
  Qed.

  Proposition make_assembly_prop_comprehension_term_unique
              {Γ X : assembly A}
              (t : assembly_term (assembly_prop_universe_type X))
              (f : assembly_morphism Γ X)
              (p : dep_assembly_morphism
                     (assembly_prop_universe_el
                        (assembly_truth_prop _))
                     (assembly_prop_universe_el
                        (subst_assembly_term f t))
                     (id_assembly_morphism _))
              (g : assembly_morphism
                     Γ
                     (mono_cod_dom (assembly_prop_comprehension_functor X t)))
              (q : comp_assembly_morphism
                     g
                     (MonicArrow
                        _
                        (mono_cod_mor (assembly_prop_comprehension_functor X t)))
                   =
                   f)
    : g = make_assembly_prop_comprehension_term t f p.
  Proof.
    use assembly_morphism_eq.
    intros x.
    use subtypePath.
    {
      intro.
      apply propproperty.
    }
    cbn.
    exact (assembly_morphism_eq_point q x).
  Qed.    
End CartesianLogic.
