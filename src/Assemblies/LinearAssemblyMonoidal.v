(**

 The monoidal fibration of linear assemblies

 We show that the linear assemblies form a fiberwise symmetric monoidal category. This means
 that we show that each fiber category is symmetric monoidal and that all the substitution
 are strong symmetric monoidal functors.

 Contents
 1. The monoidal unit of linear assemblies
 2. The monoidal product of linear assemblies
 3. Whiskering operations
 4. Unitors and associators
 5. Monoidal laws
 6. The monoidal structure on the fiber category
 7. The symmetric monoidal structure on the fiber category
 8. The substitution functors are strong symmetric monoidal functors
 9. The monoidal fibration of linear assemblies

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import FiberwiseMonoidal.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.

Local Open Scope lca.
Local Open Scope assembly.
Local Open Scope cat.

Section DependentAssemblyMonoidal.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  (** * 1. The monoidal unit of linear assemblies *)
  Definition unit_dep_assembly
             (Γ : assembly AC)
    : dep_assembly Γ.
  Proof.
    intro x.
    use make_assembly.
    - exact unitset.
    - exact (λ a _, a = I).
    - intros.
      apply setproperty.
    - intro.
      use hinhpr.
      refine (I ,, _).
      apply idpath.
  Defined.

  (** * 2. The monoidal product of linear assemblies *)
  Definition monoidal_product_lin_dep_assembly
             {Γ : assembly AC}
             (X₁ X₂ : dep_assembly Γ)
    : dep_assembly Γ.
  Proof.
    intro x.
    use make_assembly.
    - exact (X₁ x × X₂ x)%set.
    - exact (λ (a : A) (xy : X₁ x × X₂ x),
             ∃ (b₁ b₂ : A),
             b₁ ⊩ pr1 xy
             ×
             b₂ ⊩ pr2 xy
             ×
             a = (lin_pair · b₁ · b₂)%lca).
    - abstract
        (intros ;
         apply propproperty).
    - abstract
        (intros xy ;
         induction xy as [ y₁ y₂ ] ;
         pose proof (assembly_realizes_el y₁) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros ( a₁ & p₁ ) ;
         pose proof (assembly_realizes_el y₂) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros ( a₂ & p₂ ) ;
         use hinhpr ;
         refine ((lin_pair · a₁ · a₂)%lca ,, _) ;
         use hinhpr ;
         refine (a₁ ,, a₂ ,, _) ;
         simpl ;
         refine (p₁ ,, p₂ ,, _) ;
         apply idpath).
  Defined.

  (** * 3. Whiskering operations *)
  Definition lwhisker_lin_dep_assembly
             {Γ : assembly AC}
             (X : dep_assembly Γ)
             {Y₁ Y₂ : dep_assembly Γ}
             (f : lin_dep_assembly_morphism Y₁ Y₂ (id_assembly_morphism Γ))
    : lin_dep_assembly_morphism
        (monoidal_product_lin_dep_assembly X Y₁)
        (monoidal_product_lin_dep_assembly X Y₂)
        (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x yy, pr1 yy ,, f x (pr2 yy)).
    - abstract
        (pose proof (lin_dep_assembly_morphism_function_track f) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros ( a & p ) ;
         use hinhpr ;
         refine ((lca_lwhisker · a)%lca ,, _) ;
         intros x yy b₁ b₂ q ;
         use factor_through_squash_hProp ;
         intros ( c₁ & c₂ & r₁ & r₂ & r₃ ) ;
         rewrite r₃ ; clear b₂ r₃ ;
         use hinhpr ;
         refine (c₁ ,, (a · (!b₁) · c₂)%lca ,, r₁ ,, _) ;
         refine (p x (pr2 yy) b₁ c₂ q r₂ ,, _) ;
         rewrite lca_lwhisker_eq ;
         apply idpath).
  Defined.

  Definition rwhisker_lin_dep_assembly
             {Γ : assembly AC}
             (Y : dep_assembly Γ)
             {X₁ X₂ : dep_assembly Γ}
             (f : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism Γ))
    : lin_dep_assembly_morphism
        (monoidal_product_lin_dep_assembly X₁ Y)
        (monoidal_product_lin_dep_assembly X₂ Y)
        (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x yy, f x (pr1 yy) ,, pr2 yy).
    - abstract
        (pose proof (lin_dep_assembly_morphism_function_track f) as p ;
         revert p ;
         use factor_through_squash_hProp ;
         intros ( a & p ) ;
         use hinhpr ;
         refine ((lca_rwhisker · a)%lca ,, _) ;
         intros x yy b₁ b₂ q ;
         use factor_through_squash_hProp ;
         intros ( c₁ & c₂ & r₁ & r₂ & r₃ ) ;
         rewrite r₃ ; clear b₂ r₃ ;
         use hinhpr ;
         refine ((a · (!b₁) · c₁)%lca ,, c₂ ,, p x (pr1 yy) b₁ c₁ q r₁ ,, _) ;
         refine (r₂ ,, _) ;
         rewrite lca_rwhisker_eq ;
         apply idpath).
  Defined.

  Definition linear_assembly_tensor_data
             (Γ : assembly AC)
    : tensor_data ((disp_cat_of_lin_dep_assembly A) [{ Γ }]).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact monoidal_product_lin_dep_assembly.
    - exact lwhisker_lin_dep_assembly.
    - exact rwhisker_lin_dep_assembly.
  Defined.

  (** * 4. Unitors and associators *)
  Definition linear_assembly_lunitor
             {Γ : assembly AC}
             (X : dep_assembly Γ)
    : lin_dep_assembly_morphism
        (monoidal_product_lin_dep_assembly (unit_dep_assembly Γ) X)
        X
        (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, pr2 xx).
    - abstract
        (use hinhpr ;
         refine (lca_lunitor ,, _) ;
         intros x (y₁ & y₂) a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
         simpl in * ;
         rewrite q₃, q₁ ; clear q₁ q₃ ;
         rewrite lca_lunitor_eq ;
         rewrite linear_combinatory_algebra_i_eq ;
         exact q₂).
  Defined.

  Definition linear_assembly_linvunitor
             {Γ : assembly AC}
             (X : dep_assembly Γ)
    : lin_dep_assembly_morphism
        X
        (monoidal_product_lin_dep_assembly (unit_dep_assembly Γ) X)
        (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, tt ,, xx).
    - abstract
        (use hinhpr ;
         refine (B · (B · (lin_pair · I)) · K* ,, _)%lca ;
         intros x xx b₁ b₂ p₁ p₂ ;
         use hinhpr ;
         refine (I ,, b₂ ,, _) ;
         refine (idpath _ ,, _) ;
         refine (p₂ ,, _) ;
         rewrite !linear_combinatory_algebra_b_eq ;
         rewrite linear_combinatory_algebra_ks_eq ;
         apply idpath).
  Defined.

  Definition linear_assembly_runitor
             {Γ : assembly AC}
             (X : dep_assembly Γ)
    : lin_dep_assembly_morphism
        (monoidal_product_lin_dep_assembly X (unit_dep_assembly Γ))
        X
        (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, pr1 xx).
    - abstract
        (use hinhpr ;
         refine (lca_runitor ,, _) ;
         intros x (y₁ & y₂) a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
         simpl in * ; 
         rewrite q₃, q₂ ; clear q₂ q₃ ;
         rewrite lca_runitor_eq ;
         rewrite linear_combinatory_algebra_i_eq ;
         exact q₁).
  Defined.

  Definition linear_assembly_rinvunitor
             {Γ : assembly AC}
             (X : dep_assembly Γ)
    : lin_dep_assembly_morphism
        X
        (monoidal_product_lin_dep_assembly X (unit_dep_assembly Γ))
        (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, xx ,, tt).
    - abstract
        (use hinhpr ;
         refine (B · (B · (B · lca_swap · (lin_pair · I))) · K* ,, _)%lca ;
         intros x xx b₁ b₂ p₁ p₂ ;
         use hinhpr ;
         refine (b₂ ,, I ,, _) ;
         refine (p₂ ,, _) ;
         refine (idpath _ ,, _) ;
         rewrite !linear_combinatory_algebra_b_eq ;
         rewrite linear_combinatory_algebra_ks_eq ;
         rewrite lca_swap_combinator_eq ;
         apply idpath).
  Defined.

  Definition linear_assembly_lassociator
             {Γ : assembly AC}
             (X₁ X₂ X₃ : dep_assembly Γ)
    : lin_dep_assembly_morphism
        (monoidal_product_lin_dep_assembly
           (monoidal_product_lin_dep_assembly X₁ X₂)
           X₃)
        (monoidal_product_lin_dep_assembly
           X₁
           (monoidal_product_lin_dep_assembly X₂ X₃))
        (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, pr11 xx ,, pr21 xx ,, pr2 xx).
    - abstract
        (use hinhpr ;
         refine (lca_assoc_left ,, _) ;
         intros x ( (y₁ & y₂) & y₃ ) a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros ( b₁ & b₂ & q₁ & q₂ & q₃ ) ;
         revert q₁ ;
         use factor_through_squash_hProp ;
         intros ( c₁ & c₂ & r₁ & r₂ & r₃ ) ;
         use hinhpr ;
         refine (c₁ ,, (lin_pair · c₂ · b₂)%lca ,, _) ;
         refine (r₁ ,, _) ;
         rewrite q₃, r₃ ;
         rewrite lca_assoc_left_eq ;
         refine (_ ,, idpath _) ;
         use hinhpr ;
         simpl in * ;
         refine (c₂ ,, b₂ ,, r₂ ,, q₂ ,, _) ;
         apply idpath).
  Defined.

  Definition linear_assembly_rassociator
             {Γ : assembly AC}
             (X₁ X₂ X₃ : dep_assembly Γ)
    : lin_dep_assembly_morphism
        (monoidal_product_lin_dep_assembly
           X₁
           (monoidal_product_lin_dep_assembly X₂ X₃))
        (monoidal_product_lin_dep_assembly
           (monoidal_product_lin_dep_assembly X₁ X₂)
           X₃)
        (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, (pr1 xx ,, pr12 xx) ,, pr22 xx).
    - abstract
        (use hinhpr ;
         refine (lca_assoc_right ,, _) ;
         intros x ( y₁ & y₂ & y₃ ) a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros ( b₁ & b₂ & q₁ & q₂ & q₃ ) ;
         revert q₂ ;
         use factor_through_squash_hProp ;
         intros ( c₁ & c₂ & r₁ & r₂ & r₃ ) ;
         use hinhpr ;
         refine ((lin_pair · b₁ · c₁)%lca ,, c₂ ,, _) ;
         refine (hinhpr (b₁ ,, c₁ ,, q₁ ,, r₁ ,, idpath _) ,, _) ;
         simpl in * ;
         refine (r₂ ,, _) ;
         rewrite q₃, r₃ ;
         rewrite lca_assoc_right_eq ;
         apply idpath).
  Defined.
  
  Definition linear_assembly_monoidal_data
             (Γ : assembly AC)
    : monoidal_data ((disp_cat_of_lin_dep_assembly A) [{ Γ }]).
  Proof.
    use make_monoidal_data.
    - exact (linear_assembly_tensor_data Γ).
    - exact (unit_dep_assembly Γ).
    - exact linear_assembly_lunitor.
    - exact linear_assembly_linvunitor.
    - exact linear_assembly_runitor.
    - exact linear_assembly_rinvunitor.
    - exact linear_assembly_lassociator.
    - exact linear_assembly_rassociator.
  Defined.

  (** * 5. Monoidal laws *)
  Proposition linear_assembly_monoidal_laws
              (Γ : assembly AC)
    : monoidal_laws (linear_assembly_monoidal_data Γ).
  Proof.
    repeat split ;
      try intro ; intros ;
      use lin_dep_assembly_morphism_eq ; intros ? xx ;
      try (apply idpath) ;
      simpl.
    - refine (pathsinv0 _).
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (lwhisker_lin_dep_assembly _ _)
                 (lwhisker_lin_dep_assembly _ _)
                 xx).
      }
      use pathsdirprod.
      + apply idpath.
      + refine (pathsinv0 _).
        etrans.
        {
          exact (fiber_comp_lin_dep_assembly _ _ (pr2 xx)).
        }
        apply idpath.
    - refine (pathsinv0 _).
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (rwhisker_lin_dep_assembly _ _)
                 (rwhisker_lin_dep_assembly _ _)
                 xx).
      }
      use pathsdirprod.
      + refine (pathsinv0 _).
        etrans.
        {
          exact (fiber_comp_lin_dep_assembly _ _ (pr1 xx)).
        }
        apply idpath.
      + apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (rwhisker_lin_dep_assembly _ _)
                 (lwhisker_lin_dep_assembly _ _)
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (lwhisker_lin_dep_assembly _ _)
                 (rwhisker_lin_dep_assembly _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (lwhisker_lin_dep_assembly _ _)
                 (linear_assembly_lunitor _)
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lunitor _)
                 _
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lunitor _)
                 (linear_assembly_linvunitor _)
                 xx).
      }
      induction xx as [ [ ] xx ].
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_linvunitor _)
                 (linear_assembly_lunitor _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (rwhisker_lin_dep_assembly _ _)
                 (linear_assembly_runitor _)
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_runitor _)
                 _
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_runitor _)
                 (linear_assembly_rinvunitor _)
                 xx).
      }
      induction xx as [ xx [ ] ].
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_rinvunitor _)
                 (linear_assembly_runitor _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lassociator _ _ _)
                 (lwhisker_lin_dep_assembly _ (lwhisker_lin_dep_assembly _ _))
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (lwhisker_lin_dep_assembly _ _)
                 (linear_assembly_lassociator _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lassociator _ _ _)
                 (rwhisker_lin_dep_assembly _ _)
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (rwhisker_lin_dep_assembly _ (rwhisker_lin_dep_assembly _ _))
                 (linear_assembly_lassociator _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lassociator _ _ _)
                 (lwhisker_lin_dep_assembly _ (rwhisker_lin_dep_assembly _ _))
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (rwhisker_lin_dep_assembly _ (lwhisker_lin_dep_assembly _ _))
                 (linear_assembly_lassociator _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lassociator _ _ _)
                 (linear_assembly_rassociator _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_rassociator _ _ _)
                 (linear_assembly_lassociator _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lassociator _ _ _)
                 (lwhisker_lin_dep_assembly _ (linear_assembly_lunitor _))
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 _
                 (lwhisker_lin_dep_assembly _ (linear_assembly_lassociator _ _ _))
                 xx).
      }
      etrans.
      {
        apply maponpaths.
        exact (fiber_comp_lin_dep_assembly
                 _
                 _
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_lassociator _ _ _)
                 (linear_assembly_lassociator _ _ _)
                 xx).
      }
      apply idpath.
  Qed.      

  (** * 6. The monoidal structure on the fiber category *)
  Definition linear_assembly_monoidal
             (Γ : assembly AC)
    : monoidal ((disp_cat_of_lin_dep_assembly A) [{ Γ }]).
  Proof.
    simple refine (_ ,, _).
    - exact (linear_assembly_monoidal_data Γ).
    - exact (linear_assembly_monoidal_laws Γ).
  Defined.

  (** * 7. The symmetric monoidal structure on the fiber category *)
  Definition linear_assembly_monoidal_braiding
             (Γ : assembly AC)
    : braiding_data (linear_assembly_monoidal Γ).
  Proof.
    intros X₁ X₂.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, pr2 xx ,, pr1 xx).
    - abstract
        (use hinhpr ;
         refine ((K · lca_swap)%lca ,, _) ;
         intros x (y₁ & y₂) a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
         use hinhpr ;
         refine (b₂ ,, b₁ ,, _) ; simpl in * ;
         refine (q₂ ,, q₁ ,, _) ;
         rewrite q₃ ;
         rewrite !linear_combinatory_algebra_k_eq ;
         rewrite lca_swap_combinator_eq ;
         apply idpath).
  Defined.

  Proposition linear_assembly_symmetric_monoidal_laws
              (Γ : assembly AC)
    : braiding_laws
        (linear_assembly_monoidal_braiding Γ)
        (linear_assembly_monoidal_braiding Γ).
  Proof.
    repeat split ;
      try intro ; intros ;
      use lin_dep_assembly_morphism_eq ; intros ? xx ;
      simpl.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_monoidal_braiding _ _ _)
                 (rwhisker_lin_dep_assembly _ _)
                 xx).
      }
      refine (pathsinv0 _).
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (lwhisker_lin_dep_assembly _ _)
                 (linear_assembly_monoidal_braiding _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_monoidal_braiding _ _ _)
                 (lwhisker_lin_dep_assembly _ _)
                 xx).
      }
      refine (pathsinv0 _).
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (rwhisker_lin_dep_assembly _ _)
                 (linear_assembly_monoidal_braiding _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_monoidal_braiding _ _ _)
                 (linear_assembly_monoidal_braiding _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 (linear_assembly_monoidal_braiding _ _ _)
                 (linear_assembly_monoidal_braiding _ _ _)
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 _
                 (linear_assembly_lassociator _ _ _)
                 xx).
      }
      etrans.
      {
        apply maponpaths.
        exact (fiber_comp_lin_dep_assembly
                 _
                 _
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 _
                 (lwhisker_lin_dep_assembly _ (linear_assembly_monoidal_braiding _ _ _))
                 xx).
      }
      etrans.
      {
        apply maponpaths.
        exact (fiber_comp_lin_dep_assembly
                 _
                 _
                 xx).
      }
      apply idpath.
    - etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 _
                 (linear_assembly_rassociator _ _ _)
                 xx).
      }
      etrans.
      {
        apply maponpaths.
        exact (fiber_comp_lin_dep_assembly
                 _
                 _
                 xx).
      }
      apply pathsinv0.
      etrans.
      {
        exact (fiber_comp_lin_dep_assembly
                 _
                 (rwhisker_lin_dep_assembly _ (linear_assembly_monoidal_braiding _ _ _))
                 xx).
      }
      etrans.
      {
        apply maponpaths.
        exact (fiber_comp_lin_dep_assembly
                 _
                 _
                 xx).
      }
      apply idpath.
  Qed.      

  Definition linear_assembly_symmetric_monoidal
             (Γ : assembly AC)
    : symmetric (linear_assembly_monoidal Γ).
  Proof.
    simple refine (_ ,, _).
    - exact (linear_assembly_monoidal_braiding Γ).
    - exact (linear_assembly_symmetric_monoidal_laws Γ).
  Defined.

  (** * 8. The substitution functors are strong symmetric monoidal functors *)
  Definition lin_dep_assembly_cleaving_preserves_tensor
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : preserves_tensordata
        (linear_assembly_monoidal Γ₂)
        (linear_assembly_monoidal Γ₁)
        (fiber_functor_from_cleaving
           (disp_cat_of_lin_dep_assembly A)
           (lin_dep_assembly_cleaving A) s).
  Proof.
    intros X₁ X₂ ; cbn.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, xx).
    - abstract
        (use hinhpr ;
         refine (K* ,, _) ;
         intros x (y₁ & y₂) a₁ a₂ p ;
         use factor_through_squash_hProp ;
         intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
         simpl in q₁, q₂, q₃ ;
         rewrite q₃ ; clear q₃ ;
         use hinhpr ; simpl ;
         refine (b₁ ,, b₂ ,, _) ;
         refine (q₁ ,, q₂ ,, _) ;
         rewrite linear_combinatory_algebra_ks_eq ;
         apply idpath).
  Defined.

  Definition lin_dep_assembly_cleaving_preserves_unit
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : preserves_unit
        (linear_assembly_monoidal Γ₂)
        (linear_assembly_monoidal Γ₁)
        (fiber_functor_from_cleaving
           (disp_cat_of_lin_dep_assembly A)
           (lin_dep_assembly_cleaving A) s).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ _ _, tt).
    - abstract
        (use hinhpr ;
         refine (K* ,, _) ; cbn ;
         intros x xx a₁ a₂ p q ;
         rewrite q ;
         rewrite linear_combinatory_algebra_ks_eq ;
         apply idpath).
  Defined.
  
  Definition lin_dep_assembly_cleaving_preserves_fmonoidal_data
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : fmonoidal_data
        (linear_assembly_monoidal Γ₂)
        (linear_assembly_monoidal Γ₁)
        (fiber_functor_from_cleaving
           _
           (lin_dep_assembly_cleaving A)
           s).
  Proof.
    split.
    - exact (lin_dep_assembly_cleaving_preserves_tensor s).
    - exact (lin_dep_assembly_cleaving_preserves_unit s).
  Defined.

  Proposition lin_dep_assembly_cleaving_preserves_fmonoidal_laxlaws
              {Γ₁ Γ₂ : assembly AC}
              (s : assembly_morphism Γ₁ Γ₂)
    : fmonoidal_laxlaws (lin_dep_assembly_cleaving_preserves_fmonoidal_data s).
  Proof.
    repeat split ;
      intro ; intros ;
      use lin_dep_assembly_morphism_eq ; intros ? xx.
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      apply pathsinv0.
      refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      cbn -[fiber_functor_from_cleaving].
      etrans.
      {
        apply fiber_functor_from_cleaving_lin_dep_assembly.
      }
      apply pathsinv0.
      etrans.
      {
        apply maponpaths.
        apply fiber_functor_from_cleaving_lin_dep_assembly.
      }
      cbn.
      apply idpath.
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      apply pathsinv0.
      refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      cbn -[fiber_functor_from_cleaving].
      etrans.
      {
        apply fiber_functor_from_cleaving_lin_dep_assembly.
      }
      apply pathsinv0.
      etrans.
      {
        apply maponpaths_2.
        apply fiber_functor_from_cleaving_lin_dep_assembly.
      }
      cbn.
      apply idpath.
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply fiber_comp_lin_dep_assembly.
      }
      apply pathsinv0.
      refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply fiber_comp_lin_dep_assembly.
      }      
      cbn -[fiber_functor_from_cleaving].
      apply pathsinv0.
      etrans.
      {
        apply fiber_functor_from_cleaving_lin_dep_assembly.
      }
      cbn.
      apply idpath.
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply fiber_comp_lin_dep_assembly.
      }
      cbn -[fiber_functor_from_cleaving].
      etrans.
      {
        apply fiber_functor_from_cleaving_lin_dep_assembly.
      }
      cbn.
      apply idpath.
    - refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply fiber_comp_lin_dep_assembly.
      }
      cbn -[fiber_functor_from_cleaving].
      etrans.
      {
        apply fiber_functor_from_cleaving_lin_dep_assembly.
      }
      cbn.
      apply idpath.
  Qed.

  Definition lin_dep_assembly_cleaving_preserves_fmonoidal_lax
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : fmonoidal_lax
        (linear_assembly_monoidal Γ₂)
        (linear_assembly_monoidal Γ₁)
        (fiber_functor_from_cleaving
           _
           (lin_dep_assembly_cleaving A)
           s).
  Proof.
    simple refine (_ ,, _).
    - exact (lin_dep_assembly_cleaving_preserves_fmonoidal_data s).
    - exact (lin_dep_assembly_cleaving_preserves_fmonoidal_laxlaws s).
  Defined.

  Definition lin_dep_assembly_cleaving_preserves_tensor_strong
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : preserves_tensor_strongly (lin_dep_assembly_cleaving_preserves_tensor s).
  Proof.
    intros X₁ X₂.
    use make_is_z_isomorphism.
    - cbn.
      use make_lin_dep_assembly_morphism.
      + exact (λ x xx, xx).
      + abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x (y₁ & y₂) a₁ a₂ p ;
           use factor_through_squash_hProp ;
           intros (b₁ & b₂ & q₁ & q₂ & q₃) ;
           simpl in q₁, q₂, q₃ ;
           rewrite q₃ ; clear q₃ ;
           use hinhpr ; simpl ;
           refine (b₁ ,, b₂ ,, _) ;
           refine (q₁ ,, q₂ ,, _) ;
           rewrite linear_combinatory_algebra_ks_eq ;
           apply idpath).
    - abstract
        (split ;
         use lin_dep_assembly_morphism_eq ;
         intros ;
         apply fiber_comp_lin_dep_assembly).
  Defined.

  Definition lin_dep_assembly_cleaving_preserves_unit_strong
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : preserves_unit_strongly (lin_dep_assembly_cleaving_preserves_unit s).
  Proof.
    use make_is_z_isomorphism.
    - cbn.
      use make_lin_dep_assembly_morphism.
      + exact (λ _ _, tt).
      + abstract
          (use hinhpr ;
           refine (K* ,, _) ; cbn ;
           intros x xx a₁ a₂ p q ;
           rewrite q ;
           rewrite linear_combinatory_algebra_ks_eq ;
           apply idpath).
    - abstract
        (split ;
         use lin_dep_assembly_morphism_eq ;
         intros ;
         apply isapropunit).
  Defined.
  
  Definition lin_dep_assembly_cleaving_preserves_fmonoidal
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : fmonoidal
        (linear_assembly_monoidal Γ₂)
        (linear_assembly_monoidal Γ₁)
        (fiber_functor_from_cleaving
           _
           (lin_dep_assembly_cleaving A)
           s).
  Proof.
    simple refine (_ ,, _).
    - exact (lin_dep_assembly_cleaving_preserves_fmonoidal_lax s).
    - split.
      + exact (lin_dep_assembly_cleaving_preserves_tensor_strong s).
      + exact (lin_dep_assembly_cleaving_preserves_unit_strong s).
  Defined.

  Definition lin_dep_assembly_cleaving_preserves_symmetric_monoidal
             {Γ₁ Γ₂ : assembly AC}
             (s : assembly_morphism Γ₁ Γ₂)
    : is_symmetric_monoidal_functor
        (linear_assembly_symmetric_monoidal Γ₂)
        (linear_assembly_symmetric_monoidal Γ₁)
        (lin_dep_assembly_cleaving_preserves_fmonoidal s).
  Proof.
    intros X₁ X₂.
    use lin_dep_assembly_morphism_eq.
    intros x xx.
    refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
    apply pathsinv0.
    refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
    etrans.
    {
      apply fiber_functor_from_cleaving_lin_dep_assembly.
    }
    cbn.
    apply idpath.
  Qed.

  (** * 9. The monoidal fibration of linear assemblies *)
  Definition lin_dep_assembly_fiberwise_monoidal_data
    : fiberwise_monoidal_data (lin_dep_assembly_cleaving A).
  Proof.
    refine (linear_assembly_monoidal ,, _).
    exact (λ Γ₁ Γ₂ s, lin_dep_assembly_cleaving_preserves_fmonoidal s).
  Defined.

  Proposition lin_dep_assembly_fiberwise_monoidal_laws
    : fiberwise_monoidal_laws lin_dep_assembly_fiberwise_monoidal_data.
  Proof.
    split.
    - intros Γ.
      split.
      + intros X₁ X₂.
        use lin_dep_assembly_morphism_eq.
        intros x xx.
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        refine (fiber_functor_from_cleaving_identity_lin_dep_assembly _ _ @ _).
        apply pathsinv0.
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply fiber_comp_lin_dep_assembly.
        }
        cbn -[fiber_functor_from_cleaving_identity].
        etrans.
        {
          apply maponpaths.
          apply fiber_functor_from_cleaving_identity_lin_dep_assembly.
        }
        etrans.
        {
          apply maponpaths_2.
          apply fiber_functor_from_cleaving_identity_lin_dep_assembly.
        }
        apply idpath.
      + use lin_dep_assembly_morphism_eq.
        intros x xx.
        apply isapropunit.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂.
      split.
      + intros X₁ X₂.
        use lin_dep_assembly_morphism_eq.
        intros x xx ; cbn in xx.
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        refine (fiber_functor_from_cleaving_comp_lin_dep_assembly s₁ s₂ _ @ _).
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        etrans.
        {
          exact (fiber_functor_from_cleaving_lin_dep_assembly
                   s₁
                   (lin_dep_assembly_cleaving_preserves_tensor s₂ X₁ X₂)
                   xx).
        }
        apply pathsinv0.
        refine (fiber_comp_lin_dep_assembly _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply fiber_comp_lin_dep_assembly.
        }
        cbn -[fiber_functor_from_cleaving_comp].
        etrans.
        {
          apply maponpaths.
          apply fiber_functor_from_cleaving_comp_lin_dep_assembly.
        }
        etrans.
        {
          apply maponpaths_2.
          apply fiber_functor_from_cleaving_comp_lin_dep_assembly.
        }
        apply idpath.
      + use lin_dep_assembly_morphism_eq.
        intros x xx ; cbn in xx.
        apply isapropunit.
  Qed.

  Definition fiberwise_monoidal_lin_dep_assembly
    : fiberwise_monoidal (lin_dep_assembly_cleaving A).
  Proof.
    use make_fiberwise_monoidal.
    - exact lin_dep_assembly_fiberwise_monoidal_data.
    - exact lin_dep_assembly_fiberwise_monoidal_laws.
  Defined.

  Definition fiberwise_symmetric_monoidal_structure_lin_dep_assembly
    : fiberwise_symmetric_monoidal_structure
        fiberwise_monoidal_lin_dep_assembly.
  Proof.
    use make_fiberwise_symmetric_monoidal_structure.
    - exact linear_assembly_symmetric_monoidal.
    - intros Γ₁ Γ₂ s.
      exact (lin_dep_assembly_cleaving_preserves_symmetric_monoidal s).
  Defined.      

  Definition fiberwise_symmetric_monoidal_lin_dep_assembly
    : fiberwise_symmetric_monoidal (lin_dep_assembly_cleaving A).
  Proof.
    use make_fiberwise_symmetric_monoidal.
    - exact fiberwise_monoidal_lin_dep_assembly.
    - exact fiberwise_symmetric_monoidal_structure_lin_dep_assembly.
  Defined.      
End DependentAssemblyMonoidal.
