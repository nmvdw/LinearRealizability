(**

 Content
 1. The displayed category of terms in `Prop`
 2. This displayed category is a fibration
 3. Useful functions to construct morphisms
 4. Connectives
 5. Some fiberwise constructions
 6. The hyperdoctrine of propositions of assemblies
 7. Quantifiers and equality
 8. The first-order hyperdoctrine
 9. The displayed category of erms of `Prop` with linear proofs
 10. A cleaving for this displayed category
 11. Useful functions to construct linear morphisms
 12. Linear connectives
 13. Fiberwise constructions in the linear case
 14. The LNL adjunction

 split the file into:
 - displayed categories
 - connectives
 - linear connective
 - cartesian connectives
 - lnl adjunction

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
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
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
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.

Require Import PreservesMonoidalClosed.
Require Import FiberwiseMonoidal.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Basics.BIAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Types.Terms.
Require Import Types.Prop.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

Section CartesianLogic.
  Context {A : combinatory_algebra}.

  (** * 1. The displayed category of terms in `Prop` *)
  Definition assembly_prop_disp_cat_ob_mor
    : disp_cat_ob_mor (cat_of_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ, assembly_term (assembly_prop_universe_type Γ)).
    - exact (λ Γ Δ t₁ t₂ s,
             dep_assembly_morphism
               (assembly_prop_universe_el t₁)
               (assembly_prop_universe_el t₂)
               s).
  Defined.

  Definition assembly_prop_disp_cat_id_comp
    : disp_cat_id_comp
        (cat_of_assembly A)
        assembly_prop_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ Γ t, id_dep_assembly_morphism (assembly_prop_universe_el t)).
    - exact (λ Γ₁ Γ₂ Γ₃ s₁ s₂ t₁ t₂ t₃ p₁ p₂, comp_dep_assembly_morphism p₁ p₂).
  Defined.
  
  Definition assembly_prop_disp_cat_data
    : disp_cat_data (cat_of_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact assembly_prop_disp_cat_ob_mor.
    - exact assembly_prop_disp_cat_id_comp.
  Defined.

  Proposition locally_propositional_assembly_prop_disp_cat
    : locally_propositional assembly_prop_disp_cat_data.
  Proof.
    intros Γ₁ Γ₂ s t₁ t₂.
    use invproofirrelevance.
    intros p₁ p₂.
    use dep_assembly_morphism_eq.
    intros x xx.
    apply is_subsingleton_dep_assembly_assembly_prop_universe_el.
  Qed.

  Proposition assembly_prop_disp_cat_axioms
    : disp_cat_axioms (cat_of_assembly A) assembly_prop_disp_cat_data.
  Proof.
    repeat split ; intro ; intros.
    - apply locally_propositional_assembly_prop_disp_cat.
    - apply locally_propositional_assembly_prop_disp_cat.
    - apply locally_propositional_assembly_prop_disp_cat.
    - apply isasetaprop.
      apply locally_propositional_assembly_prop_disp_cat.
  Qed.
    
  Definition assembly_prop_disp_cat
    : disp_cat (cat_of_assembly A).
  Proof.
    simple refine (_ ,, _).
    - exact assembly_prop_disp_cat_data.
    - exact assembly_prop_disp_cat_axioms.
  Defined.

  (** * 2. This displayed category is a fibration *)
  Definition cleaving_assembly_prop_disp_cat_mor
             {Γ Δ : assembly A}
             (s : assembly_morphism Δ Γ)
             (t : assembly_term (assembly_prop_universe_type Γ))
    : dep_assembly_morphism
        (assembly_prop_universe_el (subst_assembly_term s t))
        (assembly_prop_universe_el t)
        s.
  Proof.
    use make_dep_assembly_morphism.
    - exact (λ x xx, xx).
    - abstract
        (use hinhpr ;
         refine (K* ,, _) ; cbn ;
         intros x xx b₁ b₂ p q ;
         rewrite combinatory_algebra_ks_eq ;
         exact q).
  Defined.
  
  Definition cleaving_assembly_prop_disp_cat
    : cleaving assembly_prop_disp_cat.
  Proof.
    intros Γ Δ s t.
    cbn in *.
    simple refine (_ ,, _).
    - exact (subst_assembly_term s t).
    - simple refine (_ ,, _).
      + exact (cleaving_assembly_prop_disp_cat_mor s t).
      + intros Δ' s' X f.
        use make_iscontr.
        * simple refine (_ ,, _).
          ** exact f.
          ** apply locally_propositional_assembly_prop_disp_cat.
        * abstract
            (intro ;
             use subtypePath ; [ intro ; apply homsets_disp | ] ;
             apply locally_propositional_assembly_prop_disp_cat).
  Defined.

  Definition is_split_cleaving_assembly_prop_disp_cat
    : is_split cleaving_assembly_prop_disp_cat.
  Proof.
    repeat split.
    - intros Γ t.
      simple refine (_ ,, _).
      + use assembly_term_eq.
        intro x ; cbn.
        apply idpath.
      + apply locally_propositional_assembly_prop_disp_cat.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
      simple refine (_ ,, _).
      + use assembly_term_eq.
        intro x ; cbn.
        apply idpath.
      + apply locally_propositional_assembly_prop_disp_cat.
    - intro Γ.
      apply isaset_assembly_term.
  Qed.

  (** * 3. Useful functions to construct morphisms *)
  Definition make_assembly_prop_proof
             {Γ : assembly A}
             {t₁ t₂ : assembly_term (assembly_prop_universe_type Γ)}
             (a : A)
             (p : ∏ (x : Γ)
                    (b₁ b₂ : A),
                  b₁ ⊩ x
                  → (t₁ x b₂ : hProp)
                  → (t₂ x (a · b₁ · b₂)%ca : hProp))
    : dep_assembly_morphism
        (assembly_prop_universe_el t₁)
        (assembly_prop_universe_el t₂)
        (id_assembly_morphism _).
  Proof.
    use make_dep_assembly_morphism.
    - intros x.
      use factor_through_squash_hProp.
      intros ( b₂ & q₂ ).
      pose proof (assembly_realizes_el x) as q.
      revert q.
      use factor_through_squash_hProp.
      intros ( b₁ & q₁ ).
      use hinhpr.
      exact ((a · b₁ · b₂)%ca ,, p x b₁ b₂ q₁ q₂).
    - use hinhpr.
      refine (a ,, _)%ca.
      intros x xx b₁ b₂ q₁ q₂ ; cbn.
      cbn in q₂.
      apply p.
      + exact q₁.
      + exact q₂.
  Qed.

  Definition assembly_prop_to_proof
             {Γ : assembly A}
             {t₁ t₂ : assembly_term (assembly_prop_universe_type Γ)}
             (φ : dep_assembly_morphism
                    (assembly_prop_universe_el t₁)
                    (assembly_prop_universe_el t₂)
                    (id_assembly_morphism _))
    : ∃ (a : A),
      ∏ (x : Γ)
        (b₁ b₂ : A),
      b₁ ⊩ x
      → (t₁ x b₂ : hProp)
      → (t₂ x (a · b₁ · b₂)%ca : hProp).
  Proof.
    pose proof (dep_assembly_morphism_function_track φ) as p.
    revert p.
    use factor_through_squash_hProp.
    intros ( a & p ).
    use hinhpr.
    refine (a ,, _)%ca.
    intros x b₁ b₂ q₁ q₂.
    exact (p x (hinhpr (b₂ ,, q₂)) b₁ b₂ q₁ q₂).
  Qed.

  Definition make_assembly_prop
             {Γ : assembly A}
             (t : Γ → A → hProp)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_term.
    - exact t.
    - abstract
        (use hinhpr ;
         refine (I ,, _) ;
         intros ; cbn ;
         exact tt).
  Defined.

  (** * 4. Connectives *)
  Definition assembly_truth_prop
             (Γ : assembly A)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, htrue).
  Defined.

  Definition assembly_false_prop
             (Γ : assembly A)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, hfalse).
  Defined.
  
  Definition assembly_conj_prop
             {Γ : assembly A}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, t₁ x (π₁ · a) ∧ t₂ x (π₂ · a))%ca.
  Defined.

  Definition assembly_disj_prop
             {Γ : assembly A}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a,
           ((K = π₁ · a) ∧ t₁ x (π₂ · a))
           ∨
           ((K* = π₁ · a) ∧ t₂ x (π₂ · a)))%ca%logic.
  Defined.
  
  Definition assembly_impl_prop
             {Γ : assembly A}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∀ (b : A), (t₁ x b : hProp) ⇒ t₂ x (a · b))%ca%logic.
  Defined.

  Definition assembly_forall_prop
             {Γ X : assembly A}
             (t : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∀ (y : X) (b : A), b ⊩ y ⇒ t (x ,, y) (a · b)%ca)%logic.
  Defined.

  Definition assembly_exists_prop
             {Γ X : assembly A}
             (t : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∃ (y : X), (π₁ · a ⊩ y)%ca ∧ t (x ,, y) (π₂ · a)%ca)%logic.
  Defined.

  Definition assembly_equality_prop
             {Γ : assembly A}
             (t : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type (prod_assembly Γ Γ)).
  Proof.
    use make_assembly_prop.
    exact (λ xy a, pr1 xy = pr2 xy ∧ t (pr1 xy) a)%logic.
  Defined.

  Definition assembly_in_prop
             (Γ : assembly A)
    : assembly_term
        (assembly_prop_universe_type
           (prod_assembly
              Γ
              (function_assembly Γ (discrete_assembly A (funset A hPropset))))).
  Proof.
    use make_assembly_prop.
    exact (λ xt a, pr12 xt (pr1 xt) a).
  Defined.

  (** * 5. Some fiberwise constructions *)
  Definition fiberwise_terminal_assembly_prop_disp_cat
    : fiberwise_terminal cleaving_assembly_prop_disp_cat.
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - exact locally_propositional_assembly_prop_disp_cat.
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

  Definition fiberwise_initial_assembly_prop_disp_cat
    : fiberwise_initial cleaving_assembly_prop_disp_cat.
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - exact locally_propositional_assembly_prop_disp_cat.
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

  Definition fiberwise_binproducts_assembly_prop_disp_cat
    : fiberwise_binproducts cleaving_assembly_prop_disp_cat.
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - exact locally_propositional_assembly_prop_disp_cat.
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
         use (make_assembly_prop_proof (pairf2 · a₁ · a₂)%ca) ;
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

  Definition fiberwise_bincoproducts_assembly_prop_disp_cat
    : fiberwise_bincoproducts cleaving_assembly_prop_disp_cat.
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - exact locally_propositional_assembly_prop_disp_cat.
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
         use (make_assembly_prop_proof (combinatory_algebra_disj_elim _ · a₁ · a₂)%ca) ;
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

  Definition fiberwise_exponentials_assembly_prop_disp_cat
    : fiberwise_exponentials fiberwise_binproducts_assembly_prop_disp_cat.
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - exact locally_propositional_assembly_prop_disp_cat.
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
         use (make_assembly_prop_proof (combinatory_algebra_impl_elim _ · a)%ca) ;
         intros x b₁ b₂ q₁ q₂ b₃ q₃ ;
         rewrite combinatory_algebra_impl_elim_eq ;
         specialize (r _ _ (pair · b₃ · b₂)%ca q₁) ;
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

  (** * 6. The hyperdoctrine of propositions of assemblies *)
  Definition assembly_prop_preorder_hyperdoctrine
    : preorder_hyperdoctrine.
  Proof.
    use make_preorder_hyperdoctrine.
    - exact (cat_of_assembly A).
    - exact assembly_prop_disp_cat.
    - exact (terminal_cat_of_assembly A).
    - exact (binproducts_cat_of_assembly A).
    - exact cleaving_assembly_prop_disp_cat.
    - exact locally_propositional_assembly_prop_disp_cat.
  Defined.

  (** * 7. Quantifiers and equality *)
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
         exact (q₃ y (π₂ · b₁)%ca q₂)).
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
         use (make_assembly_prop_proof (combinatory_algebra_all_elim _ · a)%ca) ;
         intros x b₁ b₂ q₁ q₂ y b₃ q₃ ;
         rewrite combinatory_algebra_all_elim_eq ;
         specialize (r (x ,, y) (pair · b₁ · b₃)%ca b₂) ;
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
                (combinatory_algebra_fun_pair _ · pair · π₂ · I)%ca) ;
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
         use (make_assembly_prop_proof (combinatory_algebra_ex_elim _ · a)%ca) ;
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
         use (make_assembly_prop_proof (combinatory_algebra_fun_pair _ · a · π₁ · I)%ca) ;
         cbn -[combinatory_algebra_fun_pair] ;
         intros ( x & y ) b₁ b₂ ( q₁ & q₂ ) ( r₁ & r₂ ) ;
         rewrite combinatory_algebra_fun_pair_eq ;
         rewrite combinatory_algebra_i_eq ;
         cbn in * ;
         induction r₁ ;
         exact (q x (π₁ · b₁)%ca b₂ q₁ r₂)).
  Defined.

  (** * 8. The first-order hyperdoctrine *)
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
      (use assembly_morphism_eq ;
       intros x ;
       cbn ;
       apply idpath).
  Defined.

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
         refine (combinatory_algebra_comprehension _ · a · b ,, _)%ca ;
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
        assembly_prop_disp_cat
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
        assembly_prop_disp_cat
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
    use (make_assembly_prop_proof (Λ (Co K* • V 1 • (Co π₂ • V 0)))%ca).
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

  Definition TODO { Z : UU } : Z.
  Admitted.
  
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
         refine (combinatory_algebra_comprehension_term _ · a · b ,, _)%ca ;
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

Arguments assembly_prop_disp_cat : clear implicits.
Arguments locally_propositional_assembly_prop_disp_cat : clear implicits.
Arguments cleaving_assembly_prop_disp_cat : clear implicits.
Arguments fiberwise_terminal_assembly_prop_disp_cat : clear implicits.
Arguments fiberwise_initial_assembly_prop_disp_cat : clear implicits.
Arguments fiberwise_binproducts_assembly_prop_disp_cat : clear implicits.
Arguments fiberwise_bincoproducts_assembly_prop_disp_cat : clear implicits.
Arguments fiberwise_exponentials_assembly_prop_disp_cat : clear implicits.
Arguments assembly_prop_preorder_hyperdoctrine : clear implicits.
Arguments assembly_prop_universal_quantifiers : clear implicits.
Arguments assembly_prop_existential_quantifiers : clear implicits.
Arguments assembly_prop_equality_formulas : clear implicits.
Arguments assembly_prop_first_order_preorder_hyperdoctrine : clear implicits.

Local Close Scope ca.
Local Open Scope lca.

Section LinearLogic.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  (** * 9. The displayed category of erms of `Prop` with linear proofs *)
  Definition assembly_lin_prop_disp_cat_ob_mor
    : disp_cat_ob_mor (cat_of_assembly AC).
  Proof.
    simple refine (_ ,, _).
    - exact (λ (Γ : assembly AC), assembly_term (assembly_prop_universe_type Γ)).
    - exact (λ Γ Δ t₁ t₂ s,
             lin_dep_assembly_morphism
               (assembly_prop_universe_el t₁)
               (assembly_prop_universe_el t₂)
               s).
  Defined.

  Definition assembly_lin_prop_disp_cat_id_comp
    : disp_cat_id_comp
        (cat_of_assembly AC)
        assembly_lin_prop_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ Γ t, id_lin_dep_assembly_morphism (assembly_prop_universe_el t)).
    - exact (λ Γ₁ Γ₂ Γ₃ s₁ s₂ t₁ t₂ t₃ p₁ p₂, comp_lin_dep_assembly_morphism p₁ p₂).
  Defined.
  
  Definition assembly_lin_prop_disp_cat_data
    : disp_cat_data (cat_of_assembly AC).
  Proof.
    simple refine (_ ,, _).
    - exact assembly_lin_prop_disp_cat_ob_mor.
    - exact assembly_lin_prop_disp_cat_id_comp.
  Defined.

  Proposition locally_propositional_assembly_lin_prop_disp_cat
    : locally_propositional assembly_lin_prop_disp_cat_data.
  Proof.
    intros Γ₁ Γ₂ s t₁ t₂.
    use invproofirrelevance.
    intros p₁ p₂.
    use lin_dep_assembly_morphism_eq.
    intros x xx.
    apply is_subsingleton_dep_assembly_assembly_prop_universe_el.
  Qed.

  Proposition assembly_lin_prop_disp_cat_axioms
    : disp_cat_axioms (cat_of_assembly AC) assembly_lin_prop_disp_cat_data.
  Proof.
    repeat split ; intro ; intros.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
    - apply isasetaprop.
      apply locally_propositional_assembly_lin_prop_disp_cat.
  Qed.
    
  Definition assembly_lin_prop_disp_cat
    : disp_cat (cat_of_assembly AC).
  Proof.
    simple refine (_ ,, _).
    - exact assembly_lin_prop_disp_cat_data.
    - exact assembly_lin_prop_disp_cat_axioms.
  Defined.

  (** * 10. A cleaving for this displayed category *)
  Definition cleaving_assembly_lin_prop_disp_cat_mor
             {Γ Δ : assembly AC}
             (s : assembly_morphism Δ Γ)
             (t : assembly_term (assembly_prop_universe_type Γ))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el (subst_assembly_term s t))
        (assembly_prop_universe_el t)
        s.
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, xx).
    - abstract
        (use hinhpr ;
         refine (K*%lca ,, _) ;
         intros x xx b₁ b₂ p₁ p₂ ;
         cbn ; cbn in p₂ ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact p₂).
  Defined.
  
  Definition cleaving_assembly_lin_prop_disp_cat
    : cleaving assembly_lin_prop_disp_cat.
  Proof.
    intros Γ Δ s t.
    cbn in *.
    simple refine (_ ,, _).
    - exact (subst_assembly_term (A := AC) s t).
    - simple refine (_ ,, _).
      + exact (cleaving_assembly_lin_prop_disp_cat_mor s t).
      + intros Δ' s' X f.
        use make_iscontr.
        * simple refine (_ ,, _).
          ** exact f.
          ** apply locally_propositional_assembly_lin_prop_disp_cat.
        * abstract
            (intro ;
             use subtypePath ; [ intro ; apply homsets_disp | ] ;
             apply locally_propositional_assembly_lin_prop_disp_cat).
  Defined.

  Definition is_split_cleaving_assembly_lin_prop_disp_cat
    : is_split cleaving_assembly_lin_prop_disp_cat.
  Proof.
    repeat split.
    - intros Γ t.
      simple refine (_ ,, _).
      + use assembly_term_eq.
        intro x ; cbn.
        apply idpath.
      + apply locally_propositional_assembly_lin_prop_disp_cat.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
      simple refine (_ ,, _).
      + use assembly_term_eq.
        intro x ; cbn.
        apply idpath.
      + apply locally_propositional_assembly_lin_prop_disp_cat.
    - intro Γ.
      apply isaset_assembly_term.
  Qed.

  (** * 11. Useful functions to construct linear morphisms *)
  Definition make_assembly_lin_prop_proof
             {Γ : assembly AC}
             {t₁ t₂ : assembly_term (assembly_prop_universe_type Γ)}
             (a : A)
             (p : ∏ (x : Γ)
                    (b₁ b₂ : A),
                  (b₁ ⊩ x)%lca
                  → (t₁ x b₂ : hProp)
                  → (t₂ x (a · (!b₁) · b₂)%lca : hProp))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el t₁)
        (assembly_prop_universe_el t₂)
        (id_assembly_morphism _).
  Proof.
    use make_lin_dep_assembly_morphism.
    - intros x.
      use factor_through_squash_hProp.
      intros ( b₂ & q₂ ).
      pose proof (assembly_realizes_el x) as q.
      revert q.
      use factor_through_squash_hProp.
      intros ( b₁ & q₁ ).
      use hinhpr.
      exact ((a · (!b₁) · b₂)%lca ,, p x b₁ b₂ q₁ q₂).
    - use hinhpr.
      refine (a ,, _)%ca.
      intros x xx b₁ b₂ q₁ q₂ ; cbn.
      apply p.
      + exact q₁.
      + exact q₂.
  Qed.

  Definition assembly_lin_prop_to_proof
             {Γ : assembly AC}
             {t₁ t₂ : assembly_term (assembly_prop_universe_type Γ)}
             (φ : lin_dep_assembly_morphism
                    (assembly_prop_universe_el t₁)
                    (assembly_prop_universe_el t₂)
                    (id_assembly_morphism _))
    : ∃ (a : A),
      ∏ (x : Γ)
        (b₁ b₂ : A),
      b₁ ⊩ x
      → (t₁ x b₂ : hProp)
      → (t₂ x (a · (!b₁) · b₂)%lca : hProp).
  Proof.
    pose proof (lin_dep_assembly_morphism_function_track φ) as p.
    revert p.
    use factor_through_squash_hProp.
    intros ( a & p ).
    use hinhpr.
    refine (a ,, _)%ca.
    intros x b₁ b₂ q₁ q₂.
    exact (p x (hinhpr (b₂ ,, q₂)) b₁ b₂ q₁ q₂).
  Qed.

  (** * 12. Linear connectives *)
  Definition assembly_truth_lin_prop
             (Γ : assembly AC)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, htrue).
  Defined.

  Definition assembly_false_lin_prop
             (Γ : assembly AC)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, hfalse).
  Defined.
  
  Definition assembly_unit_lin_prop
             (Γ : assembly AC)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, a = I)%logic.
  Defined.

  Definition assembly_tensor_lin_prop
             {Γ : assembly AC}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∃ (b₁ b₂ : A), (a = lin_pair · b₁ · b₂)%logic ∧ t₁ x b₁ ∧ t₂ x b₂).
  Defined.    

  Definition assembly_impl_lin_prop
             {Γ : assembly AC}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x (a : A), ∀ (b : A), (t₁ x b : hProp) ⇒ t₂ x (a · b))%logic.
  Defined.

  Definition assembly_conj_lin_prop
             {Γ : assembly AC}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ (x : Γ) (a : A),
           ∃ (b c₁ c₂ : A),
           (a = lin_pair · b · (lin_pair · (!c₁) · (!c₂)))%logic
           ∧ t₁ x (c₁ · b)
           ∧ t₂ x (c₂ · b)).
  Defined.

  Definition assembly_disj_lin_prop
             {Γ : assembly AC}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ (x : Γ) (a : A),
           ∃ (b : A),
           ((a = lin_pair · lca_bincoprod_left · b)
            ×
            (t₁ x b : hProp))
           ∨
           ((a = lin_pair · lca_bincoprod_right · b)
            ×
            (t₂ x b : hProp))).
  Defined.

  Definition assembly_lin_prop_to_prop
             {Γ : assembly AC}
             (t : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ)
    := t.

  Definition assembly_prop_to_lin_prop
             {Γ : assembly AC}
             (t : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ (x : Γ) (a : A), ∃ (b : A), (a = !b)%logic ∧ t x b).
  Defined.

  Definition assembly_lin_exists_prop
             {Γ X : assembly AC}
             (t : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a,
           ∃ (y : X)
             (b c : A),
           (a = lin_pair · (!b) · c)
           ×
           (b ⊩ y)
           ×
           (t (x ,, y) c : hProp)).
  Defined.

  (** * 13. Fiberwise constructions in the linear case *)
  Proposition assembly_lin_prop_rwhisker
              {Γ : assembly AC}
              (t₁ t₂ u : assembly_term (assembly_prop_universe_type Γ))
              (p' : lin_dep_assembly_morphism
                      (assembly_prop_universe_el t₁)
                      (assembly_prop_universe_el t₂)
                      (id_assembly_morphism _))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el (assembly_tensor_lin_prop t₁ u))
        (assembly_prop_universe_el (assembly_tensor_lin_prop t₂ u))
        (id_assembly_morphism _).
  Proof.
    pose proof (assembly_lin_prop_to_proof p') as p.
    revert p.
    use factor_through_squash ;
      [ apply locally_propositional_assembly_lin_prop_disp_cat | ].
    intros (a & p).
    clear p'.
    use (make_assembly_lin_prop_proof (lca_rwhisker · a)).
    intros x b₁ b₂ q₁.
    use factor_through_squash_hProp.
    intros (c₁ & c₂ & q₂ & q₃ & q₄).
    use hinhpr.
    specialize (p _ _ _ q₁ q₃).
    refine (a · (!b₁) · c₁ ,, c₂ ,, _ ,, _ ,, _) ; try assumption.
    rewrite q₂.
    rewrite lca_rwhisker_eq.
    apply idpath.
  Qed.

  Proposition assembly_lin_prop_lwhisker
              {Γ : assembly AC}
              (t u₁ u₂ : assembly_term (assembly_prop_universe_type Γ))
              (p' : lin_dep_assembly_morphism
                      (assembly_prop_universe_el u₁)
                      (assembly_prop_universe_el u₂)
                      (id_assembly_morphism _))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el (assembly_tensor_lin_prop t u₁))
        (assembly_prop_universe_el (assembly_tensor_lin_prop t u₂))
        (id_assembly_morphism _).
  Proof.
    pose proof (assembly_lin_prop_to_proof p') as p.
    revert p.
    use factor_through_squash ;
      [ apply locally_propositional_assembly_lin_prop_disp_cat | ].
    intros (a & p).
    clear p'.
    use (make_assembly_lin_prop_proof (lca_lwhisker · a)).
    intros x b₁ b₂ q₁.
    use factor_through_squash_hProp.
    intros (c₁ & c₂ & q₂ & q₃ & q₄).
    use hinhpr.
    specialize (p _ _ _ q₁ q₄).
    refine (c₁ ,, a · (!b₁) · c₂ ,, _ ,, q₃ ,, p).
    rewrite q₂.
    rewrite lca_lwhisker_eq.
    apply idpath.
  Qed.

  Proposition assembly_lin_prop_lunitor
              {Γ : assembly AC}
              (t : assembly_term (assembly_prop_universe_type Γ))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop (assembly_unit_lin_prop Γ) t))
        (assembly_prop_universe_el t)
        (id_assembly_morphism _).
  Proof.
    use (make_assembly_lin_prop_proof lca_lunitor).
    intros x b₁ b₂ p₁.
    use factor_through_squash_hProp.
    cbn.
    intros (c₁ & c₂ & q₂ & q₃ & q₄).
    rewrite q₂, q₃.
    rewrite lca_lunitor_eq.
    rewrite linear_combinatory_algebra_i_eq.
    exact q₄.
  Qed.

  Proposition assembly_lin_prop_linvunitor
              {Γ : assembly AC}
              (t : assembly_term (assembly_prop_universe_type Γ))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el t)
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop (assembly_unit_lin_prop Γ) t))
        (id_assembly_morphism _).
  Proof.
    use (make_assembly_lin_prop_proof
           (B · (B · (lin_pair · I)) · linear_combinatory_algebra_ks _)).
    intros x b₁ b₂ p₁ p₂.
    use hinhpr.
    refine (I ,, b₂ ,, _ ,, idpath _ ,, p₂).
    rewrite !linear_combinatory_algebra_b_eq.
    rewrite linear_combinatory_algebra_ks_eq.
    apply idpath.
  Qed.

  Proposition assembly_lin_prop_runitor
              {Γ : assembly AC}
              (t : assembly_term (assembly_prop_universe_type Γ))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop t (assembly_unit_lin_prop Γ)))
        (assembly_prop_universe_el t)
        (id_assembly_morphism _).
  Proof.
    use (make_assembly_lin_prop_proof lca_runitor).
    intros x b₁ b₂ p₁.
    use factor_through_squash_hProp.
    cbn.
    intros (c₁ & c₂ & q₂ & q₃ & q₄).
    rewrite q₂, q₄.
    rewrite lca_runitor_eq.
    rewrite linear_combinatory_algebra_i_eq.
    exact q₃.
  Qed.

  Proposition assembly_lin_prop_rinvunitor
              {Γ : assembly AC}
              (t : assembly_term (assembly_prop_universe_type Γ))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el t)
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop t (assembly_unit_lin_prop Γ)))
        (id_assembly_morphism _).
  Proof.
    use (make_assembly_lin_prop_proof
           (B · (B · (B · lca_swap · (lin_pair · I))) · linear_combinatory_algebra_ks _)).
    intros x b₁ b₂ p₁ p₂.
    use hinhpr.
    refine (b₂ ,, I ,, _ ,, p₂ ,, idpath _).
    rewrite !linear_combinatory_algebra_b_eq.
    rewrite linear_combinatory_algebra_ks_eq.
    rewrite lca_swap_combinator_eq.
    apply idpath.
  Qed.

  Proposition assembly_lin_prop_lassociator
              {Γ : assembly AC}
              (t₁ t₂ t₃ : assembly_term (assembly_prop_universe_type Γ))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop (assembly_tensor_lin_prop t₁ t₂) t₃))
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop t₁ (assembly_tensor_lin_prop t₂ t₃)))
        (id_assembly_morphism _).
  Proof.
    use (make_assembly_lin_prop_proof lca_assoc_left).
    intros x b₁ b₂ p.
    use factor_through_squash_hProp.
    intros (c₁ & c₂ & q₂ & r & q₃).
    revert r.
    use factor_through_squash_hProp.
    intros (d₁ & d₂ & r₁ & r₂ & r₃).
    use hinhpr.
    simple refine (d₁ ,, _ ,, _ ,, r₂ ,, _).
    - exact (lin_pair · d₂ · c₂).
    - rewrite q₂.
      rewrite r₁.
      rewrite lca_assoc_left_eq.
      apply idpath.
    - use hinhpr.
      refine (d₂ ,, c₂ ,, idpath _ ,, r₃ ,, q₃).
  Qed.

  Proposition assembly_lin_prop_rassociator
              {Γ : assembly AC}
              (t₁ t₂ t₃ : assembly_term (assembly_prop_universe_type Γ))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop t₁ (assembly_tensor_lin_prop t₂ t₃)))
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop (assembly_tensor_lin_prop t₁ t₂) t₃))
        (id_assembly_morphism _).
  Proof.
    use (make_assembly_lin_prop_proof lca_assoc_right).
    intros x b₁ b₂ p.
    use factor_through_squash_hProp.
    intros (c₁ & c₂ & q₂ & q₃ & r).
    revert r.
    use factor_through_squash_hProp.
    intros (d₁ & d₂ & r₁ & r₂ & r₃).
    use hinhpr.
    simple refine (lin_pair · c₁ · d₁ ,, d₂ ,, _ ,, _ ,, _).
    - rewrite q₂.
      rewrite r₁.
      rewrite lca_assoc_right_eq.
      apply idpath.
    - use hinhpr.
      exact (c₁ ,, d₁ ,, idpath _ ,, q₃ ,, r₂).
    - cbn.
      exact r₃.
  Qed.

  Definition fiberwise_monoidal_assembly_lin_prop_data
    : fiberwise_monoidal_data cleaving_assembly_lin_prop_disp_cat.
  Proof.
    use make_fiberwise_monoidal_data_locally_propositional.
    - exact locally_propositional_assembly_lin_prop_disp_cat.
    - exact (λ Γ t₁ t₂, assembly_tensor_lin_prop t₁ t₂).
    - intros Γ u t₁ t₂ p.
      exact (assembly_lin_prop_rwhisker t₁ t₂ u p).
    - intros Γ₁ t u₁ u₂ p.
      exact (assembly_lin_prop_lwhisker t u₁ u₂ p).
    - exact assembly_unit_lin_prop.
    - intros Γ t.
      exact (assembly_lin_prop_lunitor t).
    - intros Γ t.
      exact (assembly_lin_prop_linvunitor t).
    - intros Γ t.
      exact (assembly_lin_prop_runitor t).
    - intros Γ t.
      exact (assembly_lin_prop_rinvunitor t).
    - intros Γ t₁ t₂ t₃.
      exact (assembly_lin_prop_lassociator t₁ t₂ t₃).
    - intros Γ t₁ t₂ t₃.
      exact (assembly_lin_prop_rassociator t₁ t₂ t₃).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ s t₁ t₂ ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         intros x b₁ b₂ p ;
         use factor_through_squash_hProp ;
         intros (c₁ & c₂ & q₁ & q₂ & q₃) ;
         use hinhpr ;
         cbn in * ;
         refine (c₁ ,, c₂ ,, _ ,, q₂ ,, q₃) ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact q₁).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ s t₁ t₂ ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         intros x b₁ b₂ p ;
         use factor_through_squash_hProp ;
         intros (c₁ & c₂ & q₁ & q₂ & q₃) ;
         use hinhpr ;
         cbn in * ;
         refine (c₁ ,, c₂ ,, _ ,, q₂ ,, q₃) ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact q₁).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ s ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         cbn ;
         intros x b₁ b₂ q₁ q₂ ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact q₂).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ s ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         cbn ;
         intros x b₁ b₂ q₁ q₂ ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact q₂).
  Defined.
  
  Definition fiberwise_monoidal_assembly_lin_prop
    : fiberwise_monoidal cleaving_assembly_lin_prop_disp_cat.
  Proof.
    use make_fiberwise_monoidal_locally_propositional.
    - exact locally_propositional_assembly_lin_prop_disp_cat.
    - exact fiberwise_monoidal_assembly_lin_prop_data.
  Defined.

  Definition fiberwise_symmetric_monoidal_assembly_lin_prop_structure
    : fiberwise_symmetric_monoidal_structure
        fiberwise_monoidal_assembly_lin_prop.
  Proof.
    use make_fiberwise_symmetric_monoidal_structure_locally_propositional.
    - exact locally_propositional_assembly_lin_prop_disp_cat.
    - abstract
        (intros Γ t₁ t₂ ;
         cbn ;
         use (make_assembly_lin_prop_proof (K · lca_swap)) ;
         intros x a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
         use hinhpr ;
         refine (b₂ ,, b₁ ,, _ ,, q₃ ,, q₂) ;
         rewrite q₁ ;
         rewrite linear_combinatory_algebra_k_eq ;
         rewrite lca_swap_combinator_eq ;
         apply idpath).
  Defined.

  Definition fiberwise_symmetric_monoidal_assembly_lin_prop
    : fiberwise_symmetric_monoidal cleaving_assembly_lin_prop_disp_cat.
  Proof.
    use make_fiberwise_symmetric_monoidal.
    - exact fiberwise_monoidal_assembly_lin_prop.
    - exact fiberwise_symmetric_monoidal_assembly_lin_prop_structure.
  Defined.

  Definition fiberwise_symmetric_monoidal_closed_assembly_lin_prop
             (Γ : assembly AC)
    : monoidal_leftclosed
        (fiber_sym_monoidal_cat
           fiberwise_symmetric_monoidal_assembly_lin_prop
           Γ).
  Proof.
    use make_monoidal_leftclosed.
    - exact assembly_impl_lin_prop.
    - abstract
        (intros t₁ t₂ ;
         use (make_assembly_lin_prop_proof lca_eval) ;
         intros x a₁ a₂ p₁ ;
         use factor_through_squash_hProp ;
         intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
         cbn in * ;
         rewrite q₁ ;
         rewrite lca_eval_eq ;
         exact (q₂ b₂ q₃)).
    - abstract
        (intros t₁ t₂ t₃ p' ;
         pose proof (assembly_lin_prop_to_proof p') as p ;
         revert p ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_lin_prop_disp_cat | ] ;
         intros (a & p) ;
         clear p' ;
         use (make_assembly_lin_prop_proof (lca_lam · a)) ;
         intros x b₁ b₂ q₁ q₂ c q₃ ;
         rewrite lca_lam_eq ;
         apply p ; [ exact q₁ | ] ;
         use hinhpr ;
         exact (b₂ ,, c ,, idpath _ ,, q₂ ,, q₃)).
    - abstract
        (intros ; apply locally_propositional_assembly_lin_prop_disp_cat).
    - abstract
        (intros ; apply locally_propositional_assembly_lin_prop_disp_cat).
  Defined.

  Definition fiber_sym_mon_closed_cat_lin_prop
             (Γ : assembly AC)
    : sym_mon_closed_cat
    := fiber_sym_monoidal_cat fiberwise_symmetric_monoidal_assembly_lin_prop Γ
       ,,
       fiberwise_symmetric_monoidal_closed_assembly_lin_prop Γ.

  Proposition fiberwise_symmetric_monoidal_closed_assembly_lin_prop_preservation
              {Γ Δ : assembly AC}
              (s : assembly_morphism Γ Δ)
    : @preserves_sym_mon_closed
        (fiber_sym_mon_closed_cat_lin_prop Δ)
        (fiber_sym_mon_closed_cat_lin_prop Γ)
        (strong_sym_monoidal_fiber_functor
           fiberwise_symmetric_monoidal_assembly_lin_prop
           s).
  Proof.
    intros t₁ t₂.
    use make_is_z_isomorphism.
    - cbn.
      use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)).
      cbn.
      intros x a₁ a₂ p₁ p₂ b p₃.
      rewrite linear_combinatory_algebra_ks_eq.
      exact (p₂ _ p₃).
    - split ; apply locally_propositional_assembly_lin_prop_disp_cat.
  Qed.
  
  Definition fiberwise_terminal_assembly_lin_prop_disp_cat
    : fiberwise_terminal cleaving_assembly_lin_prop_disp_cat.
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - exact locally_propositional_assembly_lin_prop_disp_cat.
    - exact assembly_truth_lin_prop.
    - abstract
        (intros Γ φ ;
         use (make_assembly_lin_prop_proof I) ;
         intros ; cbn ;
         exact tt).
    - abstract
        (intros Γ₁ Γ₂ s ;
         use (make_assembly_lin_prop_proof I) ; cbn ;
         intros ;
         exact tt).
  Defined.      

  Definition fiberwise_initial_assembly_lin_prop_disp_cat
    : fiberwise_initial cleaving_assembly_lin_prop_disp_cat.
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - exact locally_propositional_assembly_lin_prop_disp_cat.
    - exact assembly_false_lin_prop.
    - abstract
        (intros Γ φ ;
         use (make_assembly_lin_prop_proof I) ; cbn ;
         intros x b₁ b₂ q xx ;
         induction xx).
    - abstract
        (intros Γ₁ Γ₂ s ;
         use (make_assembly_lin_prop_proof I) ; cbn ;
         intros x b₁ b₂ q xx ;
         induction xx).
  Defined.

  Definition fiberwise_binproducts_assembly_lin_prop_disp_cat
    : fiberwise_binproducts cleaving_assembly_lin_prop_disp_cat.
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - exact locally_propositional_assembly_lin_prop_disp_cat.
    - exact (λ Γ t₁ t₂, assembly_conj_lin_prop t₁ t₂).
    - abstract
        (cbn ;
         intros Γ t₁ t₂ ;
         use (make_assembly_lin_prop_proof lca_binprod_pr1) ;
         intros x a₁ a₂ q₁ ;
         use factor_through_squash_hProp ;
         cbn ;
         intros (a & b₁ & b₂ & q₂ & q₃ & q₄) ;
         rewrite q₂ ;
         rewrite lca_binprod_pr1_eq ;
         exact q₃).
    - abstract
        (cbn ;
         intros Γ t₁ t₂ ;
         use (make_assembly_lin_prop_proof lca_binprod_pr2) ;
         intros x a₁ a₂ q₁ ;
         use factor_through_squash_hProp ;
         cbn ;
         intros (a & b₁ & b₂ & q₂ & q₃ & q₄) ;
         rewrite q₂ ;
         rewrite lca_binprod_pr2_eq ;
         exact q₄).
    - abstract
        (cbn ;
         intros Γ t₁ t₂ u p' q' ;
         pose proof (assembly_lin_prop_to_proof p') as p ;
         revert p ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_lin_prop_disp_cat | ] ;
         intros (a₁ & p₁) ;
         clear p' ;
         pose proof (assembly_lin_prop_to_proof q') as q ;
         revert q ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_lin_prop_disp_cat | ] ;
         intros (a₂ & p₂) ;
         clear q' ;
         use (make_assembly_lin_prop_proof (lca_binprod_pair · (!a₁) · (!a₂))) ;
         intros x b₁ b₂ q₁ q₂ ;
         rewrite lca_binprod_pair_eq ;
         specialize (p₁ _ _ _ q₁ q₂) ;
         specialize (p₂ _ _ _ q₁ q₂) ;
         use hinhpr ;
         cbn ;
         exact (b₂ ,, a₁ · (!b₁) ,, a₂ · (!b₁) ,, idpath _ ,, p₁ ,, p₂)).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ s t₁ t₂ ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         intros x a₁ a₂ q₁ ;
         use factor_through_squash_hProp ;
         intros (b & c₁ & c₂ & q₂ & q₃ & q₄) ;
         use hinhpr ;
         cbn in * ;
         refine (b ,, c₁ ,, c₂ ,, _ ,, q₃ ,, q₄) ;
         rewrite linear_combinatory_algebra_ks_eq ;
         rewrite q₂ ;
         apply idpath).
  Defined.

  Definition fiberwise_bincoproducts_assembly_lin_prop_disp_cat
    : fiberwise_bincoproducts cleaving_assembly_lin_prop_disp_cat.
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - exact locally_propositional_assembly_lin_prop_disp_cat.
    - exact (λ Γ t₁ t₂, assembly_disj_lin_prop t₁ t₂).
    - abstract
        (intros Γ t₁ t₂ ;
         use (make_assembly_lin_prop_proof lca_bincoprod_inl) ;
         intros x a₁ a₂ p₁ p₂ ;
         use hinhpr ;
         refine (a₂ ,, _) ;
         use hdisj_in1 ;
         rewrite lca_bincoprod_inl_eq ;
         exact (idpath _ ,, p₂)).
    - abstract
        (intros Γ t₁ t₂ ;
         use (make_assembly_lin_prop_proof lca_bincoprod_inr) ;
         intros x a₁ a₂ p₁ p₂ ;
         use hinhpr ;
         refine (a₂ ,, _) ;
         use hdisj_in2 ;
         rewrite lca_bincoprod_inr_eq ;
         exact (idpath _ ,, p₂)).
    - abstract
        (intros Γ t₁ t₂ t₃ p₁' p₂' ;
         pose proof (assembly_lin_prop_to_proof p₁') as p₁ ;
         revert p₁ ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_lin_prop_disp_cat | ] ;
         intros (a₁ & p₁) ;
         pose proof (assembly_lin_prop_to_proof p₂') as p₂ ;
         revert p₂ ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_lin_prop_disp_cat | ] ;
         intros (a₂ & p₂) ;
         clear p₁' p₂' ;
         use (make_assembly_lin_prop_proof (lca_bincoprod_map · (!a₁) · (!a₂))) ;
         intros x b₁ b₂ q ;
         use factor_through_squash_hProp ;
         intros (c & r) ;
         revert r ;
         use factor_through_squash_hProp ;
         intros [ [ r₁ r₂ ] | [ r₁ r₂ ]] ;
         rewrite r₁ ;
         rewrite lca_bincoprod_map_eq ;
         [ rewrite lca_bincoprod_left_eq ;
           exact (p₁ _ _ _ q r₂)
         | rewrite lca_bincoprod_right_eq ;
           exact (p₂ _ _ _ q r₂) ]).
    - abstract
        (intros Γ₁ Γ₂ s t₁ t₂ ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         intros x a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (b & q) ;
         revert q ;
         use factor_through_squash_hProp ;
         intros [ [ q₁ q₂ ] | [ q₁ q₂ ]] ;
         use hinhpr ;
         refine (b ,, _) ; 
         [ use hdisj_in1 | use hdisj_in2 ] ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact (q₁ ,, q₂)).
  Defined.

  (** * 14. The LNL adjunction *)
  Proposition assembly_lin_prop_to_prop_mor
              {Γ Δ : assembly AC}
              {t₁ : assembly_term (assembly_prop_universe_type Γ)}
              {t₂ : assembly_term (assembly_prop_universe_type Δ)}
              {s : assembly_morphism Γ Δ}
              (p : lin_dep_assembly_morphism
                     (assembly_prop_universe_el t₁)
                     (assembly_prop_universe_el t₂)
                     s)
    : dep_assembly_morphism
        (assembly_prop_universe_el (assembly_lin_prop_to_prop t₁))
        (assembly_prop_universe_el (assembly_lin_prop_to_prop t₂))
        s.
  Proof.
    use make_dep_assembly_morphism.
    - exact (λ x y, p x y).
    - pose proof (lin_dep_assembly_morphism_function_track p) as q.
      revert q.
      use factor_through_squash_hProp.
      intros (a & q).
      use hinhpr.
      refine (lca_del_2 · a ,, _).
      intros x.
      simpl.
      unfold assembly_lin_prop_to_prop.
      use factor_through_squash.
      {
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros (b & r₁) c₁ c₂ r₂ r₃.
      rewrite lca_del_2_eq.
      exact (q x (hinhpr (c₂ ,, r₃)) c₁ c₂ r₂ r₃).
  Qed.
  
  Definition assembly_lin_prop_to_prop_data
    : disp_functor_data
        (functor_identity _)
        assembly_lin_prop_disp_cat
        (assembly_prop_disp_cat AC).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ t, assembly_lin_prop_to_prop t).
    - intros Γ Δ t₁ t₂ s p.
      exact (assembly_lin_prop_to_prop_mor p).
  Defined.

  Definition assembly_lin_prop_to_prop_functor
    : disp_functor
        (functor_identity _)
        assembly_lin_prop_disp_cat
        (assembly_prop_disp_cat AC).
  Proof.
    simple refine (_ ,, _).
    - exact assembly_lin_prop_to_prop_data.
    - abstract
        (split ; intros ; apply locally_propositional_assembly_prop_disp_cat).
  Defined.

  Definition is_cartesian_assembly_lin_prop_to_prop_functor
    : is_cartesian_disp_functor assembly_lin_prop_to_prop_functor.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact cleaving_assembly_lin_prop_disp_cat.
    }
    cbn.
    intros Γ₁ Γ₂ s t.
    refine (transportf
              is_cartesian
              _
              (pr22 (cleaving_assembly_prop_disp_cat AC _ _ s t))).
    apply locally_propositional_assembly_prop_disp_cat.
  Qed.
  
  Proposition assembly_prop_to_lin_prop_mor
              {Γ Δ : assembly AC}
              {t₁ : assembly_term (assembly_prop_universe_type Γ)}
              {t₂ : assembly_term (assembly_prop_universe_type Δ)}
              {s : assembly_morphism Γ Δ}
              (p : dep_assembly_morphism
                     (assembly_prop_universe_el t₁)
                     (assembly_prop_universe_el t₂)
                     s)
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el (assembly_prop_to_lin_prop t₁))
        (assembly_prop_universe_el (assembly_prop_to_lin_prop t₂))
        s.
  Proof.
    use make_lin_dep_assembly_morphism.
    - abstract
        (intros x ;
         use factor_through_squash_hProp; 
         intros (a & q) ;
         revert q ;
         use factor_through_squash_hProp ;
         intros (b & q₁ & q₂) ;
         pose proof (p x (hinhpr (b ,, q₂))) as r ;
         revert r ;
         use factor_through_squash_hProp ;
         intros (c & r) ;
         use hinhpr ;
         refine (!c ,, _) ;
         use hinhpr ;
         exact (c ,, idpath _ ,, r)).
    - pose proof (dep_assembly_morphism_function_track p) as q.
      revert q.
      use factor_through_squash_hProp.
      intros (a & q).
      use hinhpr.
      refine (lca_F_2 · (!a) ,, _).
      intros x.
      simpl.
      use factor_through_squash.
      {
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros (b & r).
      revert r.
      use factor_through_squash.
      {
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros (c & r₁ & r₂) d₁ d₂ r₃.
      use factor_through_squash.
      {
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros (d₃ & r₄ & r₅).
      use hinhpr.
      specialize (q x (hinhpr (c ,, r₂)) d₁ d₃ r₃ r₅).
      simpl in q.
      refine ((a : A) · (! d₁) · (! d₃) ,, _).
      split.
      + rewrite r₄.
        rewrite lca_F_2_eq.
        apply idpath.
      + exact q.
  Qed.

  Definition assembly_prop_to_lin_prop_data
    : disp_functor_data
        (functor_identity _)
        (assembly_prop_disp_cat AC)
        assembly_lin_prop_disp_cat.
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ t, assembly_prop_to_lin_prop t).
    - intros Γ Δ t₁ t₂ s p.
      exact (assembly_prop_to_lin_prop_mor p).
  Defined.

  Definition assembly_prop_to_lin_prop_functor
    : disp_functor
        (functor_identity _)
        (assembly_prop_disp_cat AC)
        assembly_lin_prop_disp_cat.
  Proof.
    simple refine (_ ,, _).
    - exact assembly_prop_to_lin_prop_data.
    - abstract
        (split ; intros ; apply locally_propositional_assembly_lin_prop_disp_cat).
  Defined.

  Definition is_cartesian_assembly_prop_to_lin_prop_functor
    : is_cartesian_disp_functor assembly_prop_to_lin_prop_functor.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact (cleaving_assembly_prop_disp_cat AC).
    }
    cbn.
    intros Γ₁ Γ₂ s t Δ s' t' p.
    use make_iscontr.
    - cbn in *.
      simple refine (_ ,, _) ; [ | apply locally_propositional_assembly_lin_prop_disp_cat ].
      use make_lin_dep_assembly_morphism.
      + abstract
          (intro x ;
           use factor_through_squash_hProp ;
           intros (a & q) ;
           pose proof (p x (hinhpr (a ,, q))) as r ;
           revert r ;
           use factor_through_squash_hProp ;
           intros (b & r) ;
           revert r ;
           use factor_through_squash_hProp ;
           intros (c & r₁ & r₂) ;
           use hinhpr ;
           refine (b ,, _) ;
           use hinhpr ;
           refine (c ,, _) ;
           exact (r₁ ,, r₂)).
      + pose proof (lin_dep_assembly_morphism_function_track p) as q.
        revert q.
        use factor_through_squash_hProp.
        intros (a & q).
        use hinhpr.
        refine (a ,, _).
        intros x.
        simpl.
        use factor_through_squash.
        {
          repeat (use impred ; intro).
          apply propproperty.
        }
        intros (b & r₁).
        intros c₁ c₂ r₂ r₃.
        exact (q x (hinhpr (c₂ ,, r₃)) c₁ c₂ r₂ r₃).        
    - intro.
      use subtypePath ; [ intro ; apply homsets_disp | ].
      apply locally_propositional_assembly_lin_prop_disp_cat.
  Qed.

  Definition dep_lin_assembly_prop_unit
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_identity _)
        (disp_functor_composite
           assembly_prop_to_lin_prop_functor
           assembly_lin_prop_to_prop_functor).
  Proof.
    simple refine (_ ,, _).
    - intros Γ X ; cbn.
      use (make_assembly_prop_proof (A := AC) (linear_combinatory_algebra_ks A)).
      intros x b₁ b₂ q₁ q₂.
      use hinhpr.
      simple refine (b₂ ,, _ ,, _).
      + cbn.
        rewrite linear_combinatory_algebra_ks_eq.
        apply idpath.
      + exact q₂.
    - intro ; intros.
      apply locally_propositional_assembly_prop_disp_cat.
  Qed.

  Definition dep_lin_assembly_prop_counit
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_composite
           assembly_lin_prop_to_prop_functor
           assembly_prop_to_lin_prop_functor)
        (disp_functor_identity _).
  Proof.
    simple refine (_ ,, _).
    - intros Γ X ; cbn.
      use (make_assembly_lin_prop_proof
             ((B · (B · D) · linear_combinatory_algebra_ks _)%lca)).
      intros x b₁ b₂ q₁.
      use factor_through_squash_hProp.
      intros (c & q₂ & q₃).
      rewrite !linear_combinatory_algebra_b_eq.
      rewrite linear_combinatory_algebra_ks_eq.
      rewrite q₂.
      rewrite linear_combinatory_algebra_d_eq.
      exact q₃.
    - intro ; intros.
      apply locally_propositional_assembly_lin_prop_disp_cat.
  Qed.

  Definition dep_lin_assembly_prop_adjunction_data
    : disp_adjunction_id_data
        (assembly_prop_disp_cat AC)
        assembly_lin_prop_disp_cat.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact assembly_prop_to_lin_prop_functor.
    - exact assembly_lin_prop_to_prop_functor.
    - exact dep_lin_assembly_prop_unit.
    - exact dep_lin_assembly_prop_counit.
  Defined.

  Proposition dep_lin_assembly_prop_adjunction_laws
    : form_disp_adjunction_id dep_lin_assembly_prop_adjunction_data.
  Proof.
    split.
    - intros Γ X.
      apply locally_propositional_assembly_lin_prop_disp_cat.
    - intros Γ X.
      apply locally_propositional_assembly_prop_disp_cat.
  Qed.
  
  Definition dep_lin_assembly_prop_adjunction
    : disp_adjunction_id
        (assembly_prop_disp_cat AC)
        assembly_lin_prop_disp_cat.
  Proof.
    simple refine (_ ,, _).
    - exact dep_lin_assembly_prop_adjunction_data.
    - exact dep_lin_assembly_prop_adjunction_laws.
  Defined.

  Definition fiber_functor_prop_to_lin_prop_monoidal_lax_data
             (Γ : assembly AC)
    : fmonoidal_data
        (assembly_prop_sym_monoidal_cat _)
        (fiber_sym_mon_closed_cat_lin_prop _)
        (fiber_functor assembly_prop_to_lin_prop_functor Γ).
  Proof.
    simple refine (_ ,, _).
    - intros t₁ t₂ ; cbn.
      use (make_assembly_lin_prop_proof lin_pair_to_pair).
      intros x a₁ a₂ q₁.
      use factor_through_squash_hProp.
      intros (b₁ & b₂ & q₂ & q₃ & q₄).
      revert q₃.
      use factor_through_squash_hProp.
      intros (c₁ & r₁ & r₂).
      revert q₄.
      use factor_through_squash_hProp.
      intros (c₂ & r₃ & r₄).
      use hinhpr.
      refine (((pair : AC) · c₁ · c₂)%ca ,, _).
      cbn -[lca_to_ca_applicative].
      rewrite (combinatory_algebra_pr1_pair (A := AC)).
      rewrite (combinatory_algebra_pr2_pair (A := AC)).
      rewrite q₂.
      rewrite r₁, r₃.
      rewrite lin_pair_to_pair_eq.
      exact (idpath _ ,, r₂ ,, r₄).
    - cbn.
      use (make_assembly_lin_prop_proof (C · I)%lca).
      intros x a₁ a₂ q₁ q₂.
      cbn in q₂.
      use hinhpr.
      rewrite q₂.
      rewrite linear_combinatory_algebra_c_eq.
      rewrite !linear_combinatory_algebra_i_eq.
      exact (a₁ ,, idpath _ ,, tt).
  Qed.
  
  Definition fiber_functor_prop_to_lin_prop_monoidal_lax
             (Γ : assembly AC)
    : fmonoidal_lax
        (assembly_prop_sym_monoidal_cat _)
        (fiber_sym_mon_closed_cat_lin_prop _)
        (fiber_functor assembly_prop_to_lin_prop_functor Γ).
  Proof.
    simple refine (_ ,, _).
    - exact (fiber_functor_prop_to_lin_prop_monoidal_lax_data Γ).
    - abstract
        (repeat split ;
         intro ; intros ;
         apply locally_propositional_assembly_lin_prop_disp_cat).
  Qed.

  Definition fiber_functor_prop_to_lin_prop_monoidal
             (Γ : assembly AC)
    : fmonoidal
        (assembly_prop_sym_monoidal_cat _)
        (fiber_sym_mon_closed_cat_lin_prop _)
        (fiber_functor assembly_prop_to_lin_prop_functor Γ).
  Proof.
    simple refine (_ ,, _).
    - exact (fiber_functor_prop_to_lin_prop_monoidal_lax Γ).
    - split.
      + intros t₁ t₂ ; cbn.
        use make_is_z_isomorphism ;
          [ | split ; apply locally_propositional_assembly_lin_prop_disp_cat ].
        use (make_assembly_lin_prop_proof to_lin_pair_proj).
        intros x a₁ a₂ p₁.
        use factor_through_squash_hProp.
        intros (b & p₂ & p₃).
        use hinhpr.
        refine (!((π₁ : AC)%ca · b) ,, !((π₂ : AC)%ca · b) ,, _)%lca.
        rewrite p₂.
        rewrite to_lin_pair_proj_eq.
        refine (idpath _ ,, _ ,, _).
        * use hinhpr.
          refine ((π₁ : AC)%ca · b ,, _)%lca.
          refine (idpath _ ,, _).
          exact (pr1 p₃).
        * use hinhpr.
          refine ((π₂ : AC)%ca · b ,, _)%lca.
          refine (idpath _ ,, _).
          exact (pr2 p₃).
      + use make_is_z_isomorphism ;
          [ | split ; apply locally_propositional_assembly_lin_prop_disp_cat ].
        use (make_assembly_lin_prop_proof lca_k_I).
        intros x a₁ a₂ p₁.
        use factor_through_squash_hProp.
        intros (b & p₂ & p₃).
        cbn.
        rewrite p₂.
        rewrite lca_k_I_eq.
        apply idpath.
  Qed.

  Proposition fiber_functor_prop_to_lin_prop_symmetric_monoidal
              (Γ : assembly AC)
    : is_symmetric_monoidal_functor
        (assembly_prop_sym_monoidal_cat _)
        (fiber_sym_mon_closed_cat_lin_prop _)
        (fiber_functor_prop_to_lin_prop_monoidal_lax Γ).
  Proof.
    intros t₁ t₂.
    apply locally_propositional_assembly_lin_prop_disp_cat.
  Qed.

  Definition assembly_lin_prop_preorder_hyperdoctrine
    : preorder_hyperdoctrine.
  Proof.
    use make_preorder_hyperdoctrine.
    - exact (cat_of_assembly AC).
    - exact assembly_lin_prop_disp_cat.
    - exact (terminal_cat_of_assembly AC).
    - exact (binproducts_cat_of_assembly AC).
    - exact cleaving_assembly_lin_prop_disp_cat.
    - exact locally_propositional_assembly_lin_prop_disp_cat.
  Defined.

  (** * 7. Quantifiers and equality *)
  Definition assembly_lin_prop_universal_quantifiers
    : universal_quantifiers assembly_lin_prop_preorder_hyperdoctrine.
  Proof.
    use universal_quantifiers_from_chosen.
    use make_universal_quantifiers_chosen.
    - cbn.
      exact (λ Γ X t, assembly_forall_prop t).
    - abstract
        (cbn ;
         intros Γ X t ;
         use (make_assembly_lin_prop_proof (lca_forall_intro _)) ;
         intros (x & y) b₁ b₂ (q₁ & q₂) q₃ ;
         rewrite lca_forall_intro_eq ;
         exact (q₃ _ _ q₂)).
    - abstract
        (cbn ;
         intros Γ X t₁ t₂ p ;
         pose proof (assembly_lin_prop_to_proof p) as q ;
         revert q ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_lin_prop_disp_cat | ] ;
         intros ( a & r ) ;
         clear p ;
         simpl in r ;
         use (make_assembly_lin_prop_proof (lca_forall_elim _ · a)%lca) ;
         intros x b₁ b₂ q₁ q₂ y b₃ q₃ ;
         cbn ;
         rewrite lca_forall_elim_eq ;
         specialize (r (x ,, y) ((pair : AC) · b₁ · b₃)%ca b₂) ;
         cbn in r ;
         pose (combinatory_algebra_pr1_pair (A := AC) b₁ b₃) as pth ;
         cbn in pth ;
         rewrite pth in r ;
         clear pth ;
         pose (combinatory_algebra_pr2_pair (A := AC) b₁ b₃) as pth ;
         cbn in pth ;
         rewrite pth in r ;
         clear pth ;
         exact (r (q₁ ,, q₃) q₂)).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ X s t ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         cbn ;
         intros x a₁ a₂ p₁ p₂ y b q₁ ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact (p₂ y b q₁)).
  Defined.

  Definition assembly_lin_prop_existential_quantifiers
    : existential_quantifiers assembly_lin_prop_preorder_hyperdoctrine.
  Proof.
    use existential_quantifiers_from_chosen.
    use make_existential_quantifiers_chosen.
    - cbn.
      exact (λ Γ X t, assembly_lin_exists_prop t).
    - abstract
        (cbn ;
         intros Γ X t ;
         use (make_assembly_lin_prop_proof (lca_exists_intro _)) ;
         intros (x & y) a₁ a₂ (q₁ & q₂) q₃ ;
         cbn in q₁, q₂ ;
         use hinhpr ;
         cbn ;
         rewrite lca_exists_intro_eq ;
         refine (y ,, (π₂%ca : AC) · a₁ ,, a₂ ,, _ ,, q₂ ,, q₃) ; cbn ;
         apply idpath).
    - abstract
        (intros Γ X t₁ t₂ p' ;
         pose proof (assembly_lin_prop_to_proof p') as p ;
         revert p ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_lin_prop_disp_cat | ] ;
         intros ( a & p ) ;
         clear p' ;
         cbn in p ;
         use (make_assembly_lin_prop_proof (lca_exists_elim _ · a)) ;
         intros x b₁ b₂ q₁ ;
         use factor_through_squash_hProp ;
         intros (y & c₁ & c₂ & q₂ & q₃ & q₄) ;
         specialize (p (x ,, y)) ;
         cbn in p ;
         rewrite q₂ ;
         rewrite lca_exists_elim_eq ;
         cbn ;
         specialize (p ((pair%ca : AC) · b₁ · c₁) c₂) ;
         cbn in p ;
         pose (combinatory_algebra_pr1_pair (A := AC) b₁ c₁) as pth ;
         cbn in pth ;
         rewrite pth in p ;
         clear pth ;
         pose (combinatory_algebra_pr2_pair (A := AC) b₁ c₁) as pth2 ;
         cbn in pth2 ;
         rewrite pth2 in p ;
         exact (p (q₁ ,, q₃) q₄)).
    - abstract
        (cbn ;
         intros Γ₁ Γ₂ X s t ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         intros x a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (y & b₁ & b₂ & q₁ & q₂ & q₃) ;
         use hinhpr ;
         cbn in * ;
         refine (y ,, b₁ ,, b₂ ,, _ ,, q₂ ,, q₃) ;
         rewrite q₁ ;
         rewrite linear_combinatory_algebra_ks_eq ;
         apply idpath).
  Defined.

  Proposition assembly_lin_prop_frobenius
              {Γ X : assembly AC}
              (t₁ : assembly_term (assembly_prop_universe_type Γ))
              (t₂ : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop
              t₁
              (assembly_lin_exists_prop t₂)))
        (assembly_prop_universe_el
           (assembly_lin_exists_prop
              (assembly_tensor_lin_prop
                 (subst_assembly_term
                    (pr1_assembly_morphism _ _)
                    t₁)
                 t₂)))
        (id_assembly_morphism _).
  Proof.
    use (make_assembly_lin_prop_proof lca_frobenius).
    intros x a₁ a₂ p₁.
    use factor_through_squash_hProp.
    intros (b₁ & b₂ & p₂ & p₃ & q).
    revert q.
    use factor_through_squash_hProp.
    intros (y & c₁ & c₂ & q₁ & q₂ & q₃).
    use hinhpr.
    refine (y ,, c₁ ,, lin_pair · b₁ · c₂ ,, _ ,, q₂ ,, _).
    - rewrite p₂.
      rewrite q₁.
      rewrite lca_frobenius_eq.
      apply idpath.
    - use hinhpr.
      exact (b₁ ,, c₂ ,, idpath _ ,, p₃ ,, q₃).
  Qed.

  Definition assembly_lin_prop_equality_formulas
    : equality_formulas assembly_lin_prop_preorder_hyperdoctrine.
  Proof.
    use make_equality_formulas.
    - cbn.
      exact (λ Γ t, assembly_equality_prop t).
    - abstract
        (cbn ;
         intros Γ t ;
         use (make_assembly_lin_prop_proof (linear_combinatory_algebra_ks _)) ;
         intros x b₁ b₂ q₁ q₂ ; cbn ;
         refine (idpath _ ,, _) ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact q₂).
    - abstract
        (cbn ;
         intros Γ t₁ t₂ p ;
         pose proof (assembly_lin_prop_to_proof p) as q ;
         revert q ;
         use factor_through_squash ;
         [ apply locally_propositional_assembly_lin_prop_disp_cat | ] ;
         intros ( a & q ) ;
         cbn in q ;
         use (make_assembly_lin_prop_proof (lca_equality_elim _ · a)) ;
         intros ( x & y ) b₁ b₂ ( q₁ & q₂ ) ( r₁ & r₂ ) ;
         cbn in r₁ ;
         induction r₁ ;
         rewrite lca_equality_elim_eq ;
         exact (q x ((π₁ : AC)%ca · b₁) b₂ q₁ r₂)).
  Defined.
End LinearLogic.
