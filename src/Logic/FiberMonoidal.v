(**

 Fiberwise monoidal structure

 To interpret linear logic in the realizability model, we show that the fibration
 of formulas with linear morphisms is a fiberwise monoidal fibrations. To do so,
 we show that the preorder of formulas in every context forms a symmetric monoidal
 category and that substitution preserves the symmetric monoidal structure. Note
 that since we are looking at preorders, all the necessary equations of monoidal
 categories hold vacuously.

 Content
 1. Operations on morphisms
 2. Fiberwise symmetric monoidal structure
 3. Fiberwise symmetric monoidal closed structure

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
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.

Require Import PreservesMonoidalClosed.
Require Import FiberwiseMonoidal.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Types.Terms.
Require Import Types.Prop.
Require Import Logic.Formulas.
Require Import Logic.Connectives.

Local Open Scope lca.
Local Open Scope assembly.

Section LinearLogic.
  Context (A : linear_combinatory_algebra).

  Let AC : combinatory_algebra := lca_to_ca A.
  
  (** * 1. Operations on morphisms *)
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

  (** * 2. Fiberwise symmetric monoidal structure *)
  Definition fiberwise_monoidal_assembly_lin_prop_data
    : fiberwise_monoidal_data (cleaving_assembly_lin_prop_disp_cat A).
  Proof.
    use make_fiberwise_monoidal_data_locally_propositional.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
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
    : fiberwise_monoidal (cleaving_assembly_lin_prop_disp_cat A).
  Proof.
    use make_fiberwise_monoidal_locally_propositional.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
    - exact fiberwise_monoidal_assembly_lin_prop_data.
  Defined.

  Definition fiberwise_symmetric_monoidal_assembly_lin_prop_structure
    : fiberwise_symmetric_monoidal_structure
        fiberwise_monoidal_assembly_lin_prop.
  Proof.
    use make_fiberwise_symmetric_monoidal_structure_locally_propositional.
    - apply locally_propositional_assembly_lin_prop_disp_cat.
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
    : fiberwise_symmetric_monoidal (cleaving_assembly_lin_prop_disp_cat A).
  Proof.
    use make_fiberwise_symmetric_monoidal.
    - exact fiberwise_monoidal_assembly_lin_prop.
    - exact fiberwise_symmetric_monoidal_assembly_lin_prop_structure.
  Defined.

  (** * 3. Fiberwise symmetric monoidal closed structure *)
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
End LinearLogic.
