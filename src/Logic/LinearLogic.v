(**

 Logic in realizability model (linear case)

 In this file, we show how to interpret linear logic on the type `Prop` in the linear
 realizability model. Since we defined the necessary connectives in another file, we
 only prove that these connectives satisfy the desired rule.

 Content
 1. The hyperdoctrine of formulas and linear morphisms
 2. Fiberwise terminal object
 3. Fiberwise initial object
 4. Fiberwise binary products
 5. Fiberwise binary coproducts
 6. The LNL adjunction
 7. Monoidality of the LNL adjunction
 8. The universal quantifier
 9. The existential quantifier
 10. Frobenius reciprocity
 11. Equality

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
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrineChosen.
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
Require Import Logic.Formulas.
Require Import Logic.Connectives.
Require Import Logic.CartesianLogic.
Require Import Logic.FiberMonoidal.

Local Open Scope lca.
Local Open Scope assembly.

Section LinearLogic.
  Context (A : linear_combinatory_algebra).

  Let AC : combinatory_algebra := lca_to_ca A.

  (** * 1. The hyperdoctrine of formulas and linear morphisms *)
  Definition assembly_lin_prop_preorder_hyperdoctrine
    : preorder_hyperdoctrine.
  Proof.
    use make_preorder_hyperdoctrine.
    - exact (cat_of_assembly AC).
    - exact (assembly_lin_prop_disp_cat A).
    - exact (terminal_cat_of_assembly AC).
    - exact (binproducts_cat_of_assembly AC).
    - exact (cleaving_assembly_lin_prop_disp_cat A).
    - apply locally_propositional_assembly_lin_prop_disp_cat.
  Defined.

  (** * 2. Fiberwise terminal object *)
  Definition fiberwise_terminal_assembly_lin_prop_disp_cat
    : fiberwise_terminal (cleaving_assembly_lin_prop_disp_cat A).
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
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

  (** * 3. Fiberwise initial object *)
  Definition fiberwise_initial_assembly_lin_prop_disp_cat
    : fiberwise_initial (cleaving_assembly_lin_prop_disp_cat A).
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
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

  (** * 4. Fiberwise binary products *)
  Definition fiberwise_binproducts_assembly_lin_prop_disp_cat
    : fiberwise_binproducts (cleaving_assembly_lin_prop_disp_cat A).
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
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

  (** * 5. Fiberwise binary coproducts *)
  Definition fiberwise_bincoproducts_assembly_lin_prop_disp_cat
    : fiberwise_bincoproducts (cleaving_assembly_lin_prop_disp_cat A).
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
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

  (** * 6. The LNL adjunction *)
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
        (assembly_lin_prop_disp_cat A)
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
        (assembly_lin_prop_disp_cat A)
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
      apply cleaving_assembly_lin_prop_disp_cat.
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
        (assembly_lin_prop_disp_cat A).
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
        (assembly_lin_prop_disp_cat A).
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
             ((B · (B · D) · linear_combinatory_algebra_ks _))).
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
        (assembly_lin_prop_disp_cat A).
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
        (assembly_lin_prop_disp_cat A).
  Proof.
    simple refine (_ ,, _).
    - exact dep_lin_assembly_prop_adjunction_data.
    - exact dep_lin_assembly_prop_adjunction_laws.
  Defined.

  (** * 7. Monoidality of the LNL adjunction *)
  Definition fiber_functor_prop_to_lin_prop_monoidal_lax_data
             (Γ : assembly AC)
    : fmonoidal_data
        (assembly_prop_sym_monoidal_cat _ _)
        (fiber_sym_mon_closed_cat_lin_prop _ _)
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
      refine (((pair : AC)%ca · c₁ · c₂) ,, _).
      cbn -[lca_to_ca_applicative].
      rewrite (combinatory_algebra_pr1_pair (A := AC)).
      rewrite (combinatory_algebra_pr2_pair (A := AC)).
      rewrite q₂.
      rewrite r₁, r₃.
      rewrite lin_pair_to_pair_eq.
      exact (idpath _ ,, r₂ ,, r₄).
    - cbn.
      use (make_assembly_lin_prop_proof (C · I)).
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
        (assembly_prop_sym_monoidal_cat _ _)
        (fiber_sym_mon_closed_cat_lin_prop _ _)
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
        (assembly_prop_sym_monoidal_cat _ _)
        (fiber_sym_mon_closed_cat_lin_prop _ _)
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
        refine (!((π₁ : AC)%ca · b) ,, !((π₂ : AC)%ca · b) ,, _).
        rewrite p₂.
        rewrite to_lin_pair_proj_eq.
        refine (idpath _ ,, _ ,, _).
        * use hinhpr.
          refine ((π₁ : AC)%ca · b ,, _).
          refine (idpath _ ,, _).
          exact (pr1 p₃).
        * use hinhpr.
          refine ((π₂ : AC)%ca · b ,, _).
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
        (assembly_prop_sym_monoidal_cat _ _)
        (fiber_sym_mon_closed_cat_lin_prop _ _)
        (fiber_functor_prop_to_lin_prop_monoidal_lax Γ).
  Proof.
    intros t₁ t₂.
    apply locally_propositional_assembly_lin_prop_disp_cat.
  Qed.

  (** * 8. The universal quantifier *)
  Definition assembly_lin_prop_universal_quantifiers
    : universal_quantifiers assembly_lin_prop_preorder_hyperdoctrine.
  Proof.
    use universal_quantifiers_from_chosen.
    use make_universal_quantifiers_chosen.
    - cbn.
      exact (λ Γ X t, assembly_forall_prop _ t).
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
         use (make_assembly_lin_prop_proof (lca_forall_elim _ · a)) ;
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

  (** * 9. The existential quantifier *)
  Definition assembly_lin_prop_existential_quantifiers
    : existential_quantifiers assembly_lin_prop_preorder_hyperdoctrine.
  Proof.
    use existential_quantifiers_from_chosen.
    use make_existential_quantifiers_chosen.
    - cbn.
      exact (λ Γ X t, assembly_exists_lin_prop t).
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

  (** * 10. Frobenius reciprocity *)
  Proposition assembly_lin_prop_frobenius
              {Γ X : assembly AC}
              (t₁ : assembly_term (assembly_prop_universe_type Γ))
              (t₂ : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : lin_dep_assembly_morphism
        (assembly_prop_universe_el
           (assembly_tensor_lin_prop
              t₁
              (assembly_exists_lin_prop t₂)))
        (assembly_prop_universe_el
           (assembly_exists_lin_prop
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

  (** * 11. Equality *)
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

