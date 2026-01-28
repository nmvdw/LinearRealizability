(**

 Linear ∑-types

 It is worth to note that the linear ∑-type does not give rise to a monoidal adjunction.
 In essence, this is because the formulas `(∃ (x : X), A x) ∧ (∃ (x : X), B x)` and
 `∃ (x : X), A x ∧ B x` are not equivalent. The implication goes in only one direction,
 and thus the dependent sum functor only gives rise to an oplax monoidal functor.

 Content
 1. Linear ∑-types
 2. Frobenius reciprocity
 3. Verification of the Beck-Chevalley condition

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Require Import BeckChevalleyChosen.
Require Import SetFamilies.
Require Import PreservesMonoidalClosed.
Require Import FiberwiseMonoidal.
Require Import Basics.BIAlgebra.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Combinators.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Assemblies.LinearAssemblyMonoidal.

Local Open Scope lca.
Local Open Scope assembly.
Local Open Scope cat.

Section LinearSigma.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  Section SigmaType.
    Context {Γ₁ Γ₂ : assembly AC}
            (s : assembly_morphism Γ₁ Γ₂).

    (** * 1. Linear ∑-types *)
    Definition linear_sigma_assembly
               (X : dep_assembly Γ₁)
               (y : Γ₂)
      : assembly A.
    Proof.
      use make_assembly.
      - exact (dep_sum_set_fam s X y).
      - exact (λ a xyp, ∃ (b c : A), a = lin_pair · (!b) · c × b ⊩ pr1 xyp × c ⊩ pr12 xyp)%lca.
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
           refine (lin_pair · (!a₁) · a₂ ,, _)%lca ;
           use hinhpr ;
           exact (a₁ ,, a₂ ,, idpath _ ,, Ha₁ ,, Ha₂)).
    Defined.
    
    Definition linear_sigma
               (X : dep_assembly Γ₁)
      : dep_assembly Γ₂
      := linear_sigma_assembly X.

    Definition linear_sig_pair
               (X : dep_assembly Γ₁)
      : lin_dep_assembly_morphism
          X
          (lin_dep_assembly_subst s (linear_sigma X))
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x xx, x ,, xx ,, idpath _).
      - abstract
          (use hinhpr ;
           refine (lin_pair ,, _) ;
           intros x xx a₁ a₂ p₁ p₂ ;
           use hinhpr ;
           exact (a₁ ,, a₂ ,, idpath _ ,, p₁ ,, p₂)).
    Defined.

    Definition linear_sig_elim
               {X : dep_assembly Γ₁}
               {X' : dep_assembly Γ₂}
               (g : lin_dep_assembly_morphism
                      X
                      (lin_dep_assembly_subst s X')
                      (id_assembly_morphism _))
      : lin_dep_assembly_morphism
          (linear_sigma X)
          X'
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x xyp, transportf X' (pr22 xyp) (g (pr1 xyp) (pr12 xyp))).
      - abstract
          (pose proof (lin_dep_assembly_morphism_function_track g) as p ;
           revert p ;
           use factor_through_squash_hProp ;
           intros (a & p) ;
           use hinhpr ;
           refine (lca_lin_sig_elim · a ,, _)%lca ;
           intros x (x' & y & q') b₁ b₂ q ;
           simpl in q' ; induction q' ;
           use factor_through_squash_hProp ;
           intros (c₁ & c₂ & r₁ & r₂ & r₃) ;
           cbn in * ;
           rewrite r₁ ; clear b₂ r₁ ;
           rewrite lca_lin_sig_elim_eq ;
           apply p ;
           [ exact r₂ | exact r₃ ]).
    Defined.
    
    Definition dependent_sum_lin_dep_assembly_data
               (X : dep_assembly Γ₁)
      : reflection_data
          (X : fiber_category (disp_cat_of_lin_dep_assembly A) _)
          (fiber_functor_from_cleaving
             (disp_cat_of_lin_dep_assembly A)
             (lin_dep_assembly_cleaving A)
             s).
    Proof.
      use make_reflection_data.
      - exact (linear_sigma X).
      - exact (linear_sig_pair X).
    Defined.

    Definition dependent_sum_lin_dep_assembly_laws
               (X : dep_assembly Γ₁)
      : is_reflection (dependent_sum_lin_dep_assembly_data X).
    Proof.
      intros [ X' g ] ; simpl in X', g.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           use lin_dep_assembly_morphism_eq ;
           intros x (y & xx & p) ;
           simpl in p ;
           induction p ;
           pose (lin_dep_assembly_morphism_eq_point (pathsinv0 (pr2 φ₁) @ pr2 φ₂) xx) as p ;
           refine (pathsinv0 _ @ p @ _) ;
           refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
           apply fiber_functor_from_cleaving_lin_dep_assembly).
      - simple refine (_ ,, _).
        + exact (linear_sig_elim g).
        + abstract
            (use lin_dep_assembly_morphism_eq ;
             intros x xx ;
             apply pathsinv0 ;
             refine (fiber_comp_lin_dep_assembly _ _ _ @ _) ;
             etrans ;
             [ apply fiber_functor_from_cleaving_lin_dep_assembly | ] ;
             cbn ;
             apply idpath).
    Defined.
    
    Definition dependent_sum_lin_dep_assembly
      : dependent_sum (lin_dep_assembly_cleaving A) s.
    Proof.
      use reflections_to_is_right_adjoint.
      intros X.
      use make_reflection.
      - exact (dependent_sum_lin_dep_assembly_data X).
      - exact (dependent_sum_lin_dep_assembly_laws X).
    Defined.

    Definition lin_dependent_sum_functor
      : (disp_cat_of_lin_dep_assembly A)[{Γ₁}]
        ⟶
        (disp_cat_of_lin_dep_assembly A)[{Γ₂}]
      := left_adjoint dependent_sum_lin_dep_assembly.

    Proposition lin_assembly_dependent_sum_on_mor
                {X₁ X₂ : dep_assembly Γ₁}
                (f : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism _))
                {x : Γ₂}
                (xx : linear_sigma X₁ x)
      : pr1 (#lin_dependent_sum_functor f) x xx
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
           rewrite (transportf_lin_dep_assembly_mor
                      (id_right _)
                      (comp_lin_dep_assembly_morphism f (linear_sig_pair X₂))) ;
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
            apply (transportf_lin_dep_assembly_mor
                     (id_right _)
                     (comp_lin_dep_assembly_morphism f (linear_sig_pair X₂))).
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

    Proposition lin_assembly_dependent_sum_counit
                {X : dep_assembly Γ₂}
                {x : Γ₂}
                (xx : linear_sigma (lin_dep_assembly_subst s X) x)
      : pr1 (counit_from_right_adjoint dependent_sum_lin_dep_assembly X) x xx
        =
        transportf X (dep_sum_set_fam_path xx) (dep_sum_set_fam_el xx).
    Proof.
      apply idpath.
    Qed.

    Definition linear_sum_on_tensor
               (X X' : dep_assembly Γ₁)
      : lin_dep_assembly_morphism
          (linear_sigma (monoidal_product_lin_dep_assembly X X'))
          (monoidal_product_lin_dep_assembly (linear_sigma X) (linear_sigma X'))
          (id_assembly_morphism _)
      := left_adjoint_on_tensor
           (V₁ := fiber_monoidal_cat fiberwise_monoidal_lin_dep_assembly _)
           (V₂ := fiber_monoidal_cat fiberwise_monoidal_lin_dep_assembly _)
           _
           (is_left_adjoint_left_adjoint
              dependent_sum_lin_dep_assembly)
           (lin_dep_assembly_cleaving_preserves_fmonoidal_lax _)
           X X'.

    Proposition linear_sum_on_tensor_pt
                (X X' : dep_assembly Γ₁)
                {x : Γ₂}
                (y : linear_sigma (monoidal_product_lin_dep_assembly X X') x)
      : linear_sum_on_tensor X X' x y
        =
        make_dep_sum_set_fam
          (dep_sum_set_fam_fib y)
          (pr1 (dep_sum_set_fam_el y))
          (dep_sum_set_fam_path y)
        ,,
        make_dep_sum_set_fam
          (dep_sum_set_fam_fib y)
          (pr2 (dep_sum_set_fam_el y))
          (dep_sum_set_fam_path y).
    Proof.
      unfold linear_sum_on_tensor, left_adjoint_on_tensor.
      etrans.
      {
       
        exact (fiber_comp_lin_dep_assembly
                 (#(lin_dependent_sum_functor)
                   (monoidal_cat_tensor_mor
                      (V := fiber_monoidal_cat fiberwise_monoidal_lin_dep_assembly _)
                      (linear_sig_pair X)
                      (linear_sig_pair X'))
                  · #(lin_dependent_sum_functor)
                     (lin_dep_assembly_cleaving_preserves_tensor _ _ _))
                 (counit_from_right_adjoint dependent_sum_lin_dep_assembly _)
                 y).
      }
      etrans.
      {
        apply maponpaths.
        apply fiber_comp_lin_dep_assembly.
      }      
      rewrite !lin_assembly_dependent_sum_on_mor.
      rewrite lin_assembly_dependent_sum_counit.
      induction y as [ y [ yy p ]].
      simpl in p.
      induction p.
      use dirprodeq.
      - etrans.
        {
          apply (pr1_transportf (B := linear_sigma X)).
        }
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (transportf_lin_dep_assembly_mor
                   _
                   (comp_lin_dep_assembly_morphism
                      (rwhisker_lin_dep_assembly X' (linear_sig_pair X))
                      (lwhisker_lin_dep_assembly
                         (lin_dep_assembly_subst s (linear_sigma X))
                         (linear_sig_pair X')))).
        }
        cbn.
        rewrite transportf_set.
        {
          apply idpath.
        }
        apply setproperty.
      - etrans.
        {
          apply (pr2_transportf (B1 := linear_sigma X) (B2 := linear_sigma X')).
        }
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (transportf_lin_dep_assembly_mor
                   _
                   (comp_lin_dep_assembly_morphism
                      (rwhisker_lin_dep_assembly X' (linear_sig_pair X))
                      (lwhisker_lin_dep_assembly
                         (lin_dep_assembly_subst s (linear_sigma X))
                         (linear_sig_pair X')))).
        }
        cbn.
        rewrite transportf_set.
        {
          apply idpath.
        }
        apply setproperty.
    Qed.

    (** * 2. Frobenius reciprocity *)
    Definition lin_assembly_frobenius_morphism
               (X : dep_assembly Γ₁)
               (X' : dep_assembly Γ₂)
      : lin_dep_assembly_morphism
          (linear_sigma
             (monoidal_product_lin_dep_assembly
                (lin_dep_assembly_subst s X')
                X))
          (monoidal_product_lin_dep_assembly
             X'
             (linear_sigma X))
          (id_assembly_morphism _)
      := fiber_comp_lin_dep_assembly_morphism
           (linear_sum_on_tensor _ _)
           (rwhisker_lin_dep_assembly
              _
              (counit_from_right_adjoint dependent_sum_lin_dep_assembly _)).

    Proposition lin_assembly_frobenius_morphism_pt
                {X : dep_assembly Γ₁}
                {X' : dep_assembly Γ₂}
                {x : Γ₂}
                (xx : linear_sigma
                        (monoidal_product_lin_dep_assembly
                           (lin_dep_assembly_subst s X')
                           X)
                        x)
      : lin_assembly_frobenius_morphism X X' x xx
        =
        transportf X' (pr22 xx) (pr112 xx)
        ,,
        make_dep_sum_set_fam _ (pr212 xx) (pr22 xx).
    Proof.
      unfold lin_assembly_frobenius_morphism.
      refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply linear_sum_on_tensor_pt.
      }
      apply idpath.
    Qed.
        
    Definition lin_assembly_frobenius_morphism_inv
               (X : dep_assembly Γ₁)
               (X' : dep_assembly Γ₂)
      : lin_dep_assembly_morphism
          (monoidal_product_lin_dep_assembly
             X'
             (linear_sigma X))
          (linear_sigma
             (monoidal_product_lin_dep_assembly
                (lin_dep_assembly_subst s X')
                X))
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x yy, pr12 yy ,, (transportb X' (pr222 yy) (pr1 yy) ,, pr122 yy) ,, pr222 yy).
      - abstract
          (use hinhpr ;
           refine (lca_frobenius ,, _) ;
           intros x (xx & y & yy & p) a₁ a₂ p' ; cbn in p ;
           cbn -[ishinh] ;
           use factor_through_squash_hProp ;
           intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
           rewrite q₃ ; clear a₂ q₃ ;
           revert q₂ ;
           use factor_through_squash_hProp ;
           intros (c₁ & c₂ & r₁ & r₂ & r₃) ;
           rewrite r₁ ; clear b₂ r₁ ;
           use hinhpr ;
           refine (c₁ ,, _) ;
           refine (lin_pair · b₁ · c₂ ,, _)%lca ;
           rewrite lca_frobenius_eq ;
           refine (idpath _ ,, r₂ ,, _) ;
           use hinhpr ;
           refine (b₁ ,, c₂ ,, _) ;
           repeat split ; try assumption ;
           unfold transportb ;
           use dep_assembly_transportf_realizes ;
           exact q₁).
    Defined.

    Proposition is_z_isomorphism_lin_assembly_frobenius_morphism_laws
                (X : dep_assembly Γ₁)
                (X' : dep_assembly Γ₂)
      : is_inverse_in_precat
          (C := (disp_cat_of_lin_dep_assembly A)[{_}])
          (lin_assembly_frobenius_morphism X X')
          (lin_assembly_frobenius_morphism_inv X X').
    Proof.
      split.
      - use lin_dep_assembly_morphism_eq.
        intros x (y & (xx₁ & xx₂) & p).
        simpl in p.
        induction p.
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply lin_assembly_frobenius_morphism_pt.
        }
        cbn.
        apply idpath.
      - use lin_dep_assembly_morphism_eq.
        intros x (xx & y & yy & p).
        cbn in p.
        induction p.
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        etrans.
        {
          apply lin_assembly_frobenius_morphism_pt.
        }
        cbn.
        apply idpath.
    Qed.
    
    Definition is_z_isomorphism_lin_assembly_frobenius_morphism
               (X : dep_assembly Γ₁)
               (X' : dep_assembly Γ₂)
      : is_z_isomorphism
          (C := (disp_cat_of_lin_dep_assembly A)[{_}])
          (lin_assembly_frobenius_morphism X X').
    Proof.
      use make_is_z_isomorphism.
      - exact (lin_assembly_frobenius_morphism_inv X X').
      - exact (is_z_isomorphism_lin_assembly_frobenius_morphism_laws X X').
    Defined.
  End SigmaType.

  (** * 3. Verification of the Beck-Chevalley condition *)
  Section BeckChevalley.
    Context {Γ₁ Γ₂ Γ₃ : assembly AC}
            {f₁ : assembly_morphism Γ₂ Γ₁}
            {f₂ : assembly_morphism Γ₃ Γ₁}
            (X : dep_assembly Γ₂).

    Let Γ₄ : assembly AC := pullback_assembly (A := AC) f₁ f₂.
    Let p₁ : assembly_morphism Γ₄ Γ₂ := pullback_assembly_pr1 (A := AC) f₁ f₂.
    Let p₂ : assembly_morphism Γ₄ Γ₃ := pullback_assembly_pr2 (A := AC) f₁ f₂.
    Let e : comp_assembly_morphism (A := AC) p₁ f₁
            =
            comp_assembly_morphism (A := AC) p₂ f₂
      := PullbackSqrCommutes (pullbacks_cat_of_assembly AC Γ₁ Γ₂ Γ₃ f₁ f₂).

    Proposition left_beck_chevalley_nat_trans_lin_dep_assembly_path
                {x : Γ₃}
                (xx : dep_sum_set_fam p₂ (λ (x : pullback_assembly (A := AC) f₁ f₂), X (p₁ x)) x)
      : f₁ (pr1 (dep_sum_set_fam_fib xx)) = f₂ x.
    Proof.
      refine (_ @ maponpaths f₂ (pr22 xx)).      
      exact (assembly_morphism_eq_point e (pr1 xx)).
    Qed.
    
    Proposition left_beck_chevalley_nat_trans_lin_dep_assembly
                {x : Γ₃}
                (xx : dep_sum_set_fam p₂ (λ (x : pullback_assembly (A := AC) f₁ f₂), X (p₁ x)) x)
      : pr1 (left_beck_chevalley_nat_trans
               (dependent_sum_lin_dep_assembly f₁)
               (dependent_sum_lin_dep_assembly p₂)
               (comm_nat_z_iso (lin_dep_assembly_cleaving A) f₁ f₂ p₂ p₁ e)
               X)
          x
          xx
        =
        make_dep_sum_set_fam
          (p₁ (dep_sum_set_fam_fib xx))
          (dep_sum_set_fam_el xx)
          (left_beck_chevalley_nat_trans_lin_dep_assembly_path xx).
    Proof.
      pose (left_beck_chevalley_nat_trans_ob
              (dependent_sum_lin_dep_assembly f₁)
              (dependent_sum_lin_dep_assembly p₂)
              (comm_nat_z_iso (lin_dep_assembly_cleaving A) f₁ f₂ p₂ p₁ e)
              X)
        as q.
      rewrite q.
      clear q.
      etrans.
      {
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        apply maponpaths.
        apply fiber_comp_lin_dep_assembly.
      }
      etrans.
      {
        do 2 apply maponpaths.
        exact (lin_assembly_dependent_sum_on_mor _ _ _).
      }
      etrans.
      {
        apply maponpaths.
        exact (lin_assembly_dependent_sum_on_mor _ _ _).
      }
      etrans.
      {
        apply lin_assembly_dependent_sum_counit.
      }
      etrans.
      {
        cbn -[fiber_functor_from_cleaving comm_nat_z_iso].
        apply maponpaths.
        exact (comm_nat_z_iso_lin_dep_assembly _ _).
      }
      etrans.
      {
        do 2 apply maponpaths.
        exact (fiber_functor_from_cleaving_lin_dep_assembly _ _ _).
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
    
    Definition lin_dep_assembly_sum_bc_isomorphism
      : lin_dep_assembly_morphism
          (linear_sigma p₂ (lin_dep_assembly_subst p₁ X))
          (lin_dep_assembly_subst f₂ (linear_sigma f₁ X))
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
      - refine (λ x xyp, make_dep_sum_set_fam _ _ _).
        + exact (dep_sum_set_fam_el xyp).
        + apply left_beck_chevalley_nat_trans_lin_dep_assembly_path.
      - abstract
          (use hinhpr ;
           simple refine (lca_lin_sum_bc ,, _) ;
           intros x ((x' & y' & r) & z & r') a₁ a₂ p ;
           cbn in z, r' ;
           induction r' ;
           use factor_through_squash_hProp ;
           intros (b₁ & b₂ & q₁ & (q₂ & q₃) & q₄) ;
           use hinhpr ; cbn in * ;
           rewrite q₁ ; clear a₂ q₁ ;
           refine ((π₁ : AC)%ca · b₁ ,, b₂ ,, _)%lca ;
           rewrite lca_lin_sum_bc_eq ;
           repeat split ;
           assumption).
    Defined.

    Definition lin_dep_assembly_sum_bc_isomorphism_inv
      : lin_dep_assembly_morphism
          (lin_dep_assembly_subst f₂ (linear_sigma f₁ X))
          (linear_sigma p₂ (lin_dep_assembly_subst p₁ X))
          (id_assembly_morphism _).
    Proof.
      use make_lin_dep_assembly_morphism.
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
           simple refine (lca_lin_sum_bc_inv ,, _) ;
           intros x (y & yy & p') a₁ a₂ p ; cbn in p' ;
           use factor_through_squash_hProp ;
           intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
           use hinhpr ;
           cbn -[lca_to_ca] in * ;
           rewrite q₁ ; clear a₂ q₁ ;
           refine (((pair : AC)%ca · b₁  · a₁)%lca ,, b₂ ,, _) ;
           rewrite (combinatory_algebra_pr1_pair (A := AC)) ;
           rewrite (combinatory_algebra_pr2_pair (A := AC)) ;
           rewrite lca_lin_sum_bc_inv_eq ;
           repeat split ;
           assumption).
    Defined.

    Proposition is_z_isomorphism_lin_dep_assembly_sum_bc_isomorphism_invs
      : is_inverse_in_precat
          (C := (disp_cat_of_lin_dep_assembly A)[{Γ₃}])
          lin_dep_assembly_sum_bc_isomorphism
          lin_dep_assembly_sum_bc_isomorphism_inv.
    Proof.
      split.
      - use lin_dep_assembly_morphism_eq.
        intros x xx.
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
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
      - use lin_dep_assembly_morphism_eq.
        intros x xx.
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        cbn.
        induction xx as [ y [ yy p ]].
        cbn in *.
        do 2 apply maponpaths.
        apply setproperty.
    Qed.
    
    Definition is_z_isomorphism_lin_dep_assembly_sum_bc_isomorphism
      : is_z_isomorphism
          (C := (disp_cat_of_lin_dep_assembly A)[{Γ₃}])
          lin_dep_assembly_sum_bc_isomorphism.
    Proof.
      use make_is_z_isomorphism.
      - exact lin_dep_assembly_sum_bc_isomorphism_inv.
      - exact is_z_isomorphism_lin_dep_assembly_sum_bc_isomorphism_invs.
    Defined.

    Definition is_z_iso_left_beck_chevalley_nat_trans_lin_dep_assembly
      : is_z_isomorphism
          (left_beck_chevalley_nat_trans
             (dependent_sum_lin_dep_assembly f₁)
             (dependent_sum_lin_dep_assembly p₂)
             (comm_nat_z_iso (lin_dep_assembly_cleaving A) f₁ f₂ p₂ p₁ e)
             X).
    Proof.
      use is_z_isomorphism_path.
      - exact lin_dep_assembly_sum_bc_isomorphism.
      - abstract
          (use lin_dep_assembly_morphism_eq ;
           intros y yy ;
           refine (pathsinv0 _) ;
           apply (left_beck_chevalley_nat_trans_lin_dep_assembly yy)).
      - exact is_z_isomorphism_lin_dep_assembly_sum_bc_isomorphism.
    Defined.
  End BeckChevalley.

  Definition lin_dep_assembly_dependent_sums
    : has_dependent_sums (lin_dep_assembly_cleaving A).
  Proof.
    use has_dependent_sums_chosen_to_dependent_sum.
    - exact (pullbacks_cat_of_assembly AC).
    - use make_has_dependent_sums_chosen.
      + exact (λ _ _ s, dependent_sum_lin_dep_assembly s).
      + cbn.
        intros Γ₁ Γ₂ Γ₃ f₁ f₂ X.
        apply is_z_iso_left_beck_chevalley_nat_trans_lin_dep_assembly.
  Defined.
End LinearSigma.
