(**

 Linear assemblies

 Contents
 1. Linear morphisms between assemblies
 2. Identity and composition of linear dependent assembly morphisms
 3. The displayed category of linear dependent assemblies
 4. The cleaving for linear dependent assemblies
 5. Some equational lemmas
 6. The fiberwise terminal object

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
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.DependentAssembly.

Local Open Scope lca.
Local Open Scope assembly.
Local Open Scope cat.

Section DependentAssembly.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  (** * 1. Linear morphisms between assemblies *)
  Definition tracks_lin_dep_assembly_morphism
             {Γ₁ Γ₂ : assembly AC}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : ∏ (x : Γ₁), X₁ x → X₂ (s x))
             (a : A)
    : UU
    := ∏ (x : Γ₁)
         (xx : X₁ x)
         (b₁ b₂ : A),
       b₁ ⊩ x
       →
       b₂ ⊩ xx
       →
       (a · (!b₁) · b₂)%ca ⊩ f x xx.

  Proposition isaprop_tracks_lin_dep_assembly_morphism
              {Γ₁ Γ₂ : assembly AC}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              (f : ∏ (x : Γ₁), X₁ x → X₂ (s x))
              (a : A)
    : isaprop (tracks_lin_dep_assembly_morphism f a).
  Proof.
    repeat (use impred ; intro).
    apply propproperty.
  Qed.
  
  Definition lin_dep_assembly_morphism_tracker
             {Γ₁ Γ₂ : assembly AC}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : ∏ (x : Γ₁), X₁ x → X₂ (s x))
    : hProp
    := ∃ (a : A), tracks_lin_dep_assembly_morphism f a.

  Definition lin_dep_assembly_morphism
             {Γ₁ Γ₂ : assembly AC}
             (X₁ : dep_assembly Γ₁)
             (X₂ : dep_assembly Γ₂)
             (s : assembly_morphism Γ₁ Γ₂)
    : UU
    := ∑ (f : ∏ (x : Γ₁), X₁ x → X₂ (s x)),
       lin_dep_assembly_morphism_tracker f.

  Proposition isaset_lin_dep_assembly_morphism
              {Γ₁ Γ₂ : assembly AC}
              (X₁ : dep_assembly Γ₁)
              (X₂ : dep_assembly Γ₂)
              (s : assembly_morphism Γ₁ Γ₂)
    : isaset (lin_dep_assembly_morphism X₁ X₂ s).
  Proof.
    use isaset_total2.
    - do 2 (use impred_isaset ; intro).
      apply setproperty.
    - intros.
      apply isasetaprop.
      apply propproperty.
  Qed.
  
  Definition make_lin_dep_assembly_morphism
             {Γ₁ Γ₂ : assembly AC}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : ∏ (x : Γ₁), X₁ x → X₂ (s x))
             (Hf : lin_dep_assembly_morphism_tracker f)
    : lin_dep_assembly_morphism X₁ X₂ s
    := f ,, Hf.

  Definition lin_dep_assembly_morphism_function
             {Γ₁ Γ₂ : assembly AC}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {s : assembly_morphism Γ₁ Γ₂}
             (f : lin_dep_assembly_morphism X₁ X₂ s)
             (x : Γ₁)
             (xx : X₁ x)
    : X₂ (s x)
    := pr1 f x xx.

  Coercion lin_dep_assembly_morphism_function : lin_dep_assembly_morphism >-> Funclass.

  Proposition lin_dep_assembly_morphism_function_track
              {Γ₁ Γ₂ : assembly AC}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              (f : lin_dep_assembly_morphism X₁ X₂ s)
    : lin_dep_assembly_morphism_tracker f.
  Proof.
    exact (pr2 f).
  Defined.

  Proposition lin_dep_assembly_morphism_eq
              {Γ₁ Γ₂ : assembly AC}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              {f g : lin_dep_assembly_morphism X₁ X₂ s}
              (p : ∏ (x : Γ₁) (xx : X₁ x), f x xx = g x xx)
    : f = g.
  Proof.
    use subtypePath_prop.
    use funextsec ; intro x.
    use funextsec ; intro xx.
    exact (p x xx).
  Qed.

  Proposition lin_dep_assembly_morphism_eq_point
              {Γ₁ Γ₂ : assembly AC}
              {X₁ : dep_assembly Γ₁}
              {X₂ : dep_assembly Γ₂}
              {s : assembly_morphism Γ₁ Γ₂}
              {f g : lin_dep_assembly_morphism X₁ X₂ s}
              (p : f = g)
              {x : Γ₁}
              (xx : X₁ x)
    : f x xx = g x xx.
  Proof.
    induction p.
    apply idpath.
  Qed.

  (** * 2. Identity and composition of linear dependent assembly morphisms *)
  Definition id_lin_dep_assembly_morphism
             {Γ : assembly AC}
             (X : dep_assembly Γ)
    : lin_dep_assembly_morphism X X (id_assembly_morphism Γ).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, xx).
    - abstract
        (use hinhpr ;
         refine (K* ,, _) ;
         intros x xx b₁ b₂ p₁ p₂ ;
         rewrite linear_combinatory_algebra_ks_eq ;
         exact p₂).
  Defined.

  Definition comp_lin_dep_assembly_morphism
             {Γ₁ Γ₂ Γ₃ : assembly AC}
             {s₁ : assembly_morphism Γ₁ Γ₂}
             {s₂ : assembly_morphism Γ₂ Γ₃}
             {X₁ : dep_assembly Γ₁}
             {X₂ : dep_assembly Γ₂}
             {X₃ : dep_assembly Γ₃}
             (f : lin_dep_assembly_morphism X₁ X₂ s₁)
             (g : lin_dep_assembly_morphism X₂ X₃ s₂)
    : lin_dep_assembly_morphism X₁ X₃ (comp_assembly_morphism s₁ s₂).
  Proof.
    use make_lin_dep_assembly_morphism.
    - exact (λ x xx, g _ (f x xx)).
    -   (pose proof (lin_dep_assembly_morphism_function_track f) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros ( a_f & p_f ) ;
         pose proof (lin_dep_assembly_morphism_function_track g) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros ( a_g & p_g ) ;
         pose proof (assembly_morphism_tracked s₁) as q ;
         revert q ;
         use factor_through_squash_hProp ;
         intros ( a_s & p_s ) ;
         use hinhpr).
        refine ((Bd · a_g · a_f · !a_s) ,, _)%lca.
        intros x xx b₁ b₂ q₁ q₂.
        rewrite lin_dep_comp_eq.
        use p_g.
        + exact (p_s b₁ x q₁).
        + use p_f ; assumption.
  Defined.

  (** * 3. The displayed category of linear dependent assemblies *)
  Definition disp_cat_of_lin_dep_assembly_ob_mor
    : disp_cat_ob_mor (cat_of_assembly AC).
  Proof.
    simple refine (_ ,, _).
    - exact dep_assembly.
    - exact (λ Γ₁ Γ₂ X₁ X₂ s, lin_dep_assembly_morphism X₁ X₂ s).
  Defined.

  Definition disp_cat_of_lin_dep_assembly_id_comp
    : disp_cat_id_comp
        (cat_of_assembly AC)
        disp_cat_of_lin_dep_assembly_ob_mor.
  Proof.
    split.
    - intros Γ X.
      exact (id_lin_dep_assembly_morphism X).
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ X₁ X₂ X₃ f g.
      exact (comp_lin_dep_assembly_morphism f g).
  Defined.      
      
  Definition disp_cat_of_lin_dep_assembly_data
    : disp_cat_data (cat_of_assembly AC).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_lin_dep_assembly_ob_mor.
    - exact disp_cat_of_lin_dep_assembly_id_comp.
  Defined.

  Proposition transportf_lin_dep_assembly_mor
              {Γ₁ Γ₂ : cat_of_assembly AC}
              {s s' : Γ₁ --> Γ₂}
              (p : s' = s)
              {X₁ : disp_cat_of_lin_dep_assembly_data Γ₁}
              {X₂ : pr1 disp_cat_of_lin_dep_assembly_data Γ₂}
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

  Proposition transportb_lin_dep_assembly_mor
              {Γ₁ Γ₂ : cat_of_assembly AC}
              {s s' : Γ₁ --> Γ₂}
              (p : s = s')
              {X₁ : disp_cat_of_lin_dep_assembly_data Γ₁}
              {X₂ : pr1 disp_cat_of_lin_dep_assembly_data Γ₂}
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

  Proposition disp_cat_of_lin_dep_assembly_axioms
    : disp_cat_axioms
        (cat_of_assembly AC)
        disp_cat_of_lin_dep_assembly_data.
  Proof.
    repeat split.
    - intros.
      use lin_dep_assembly_morphism_eq.
      intros.
      refine (_ @ pathsinv0 (transportb_lin_dep_assembly_mor _ _ _)).
      apply pathsinv0.
      unfold transportb.
      rewrite transportf_set.
      {
        apply idpath.
      }
      apply setproperty.
    - intros.
      use lin_dep_assembly_morphism_eq.
      intros.
      refine (_ @ pathsinv0 (transportb_lin_dep_assembly_mor _ _ _)).
      apply pathsinv0.
      unfold transportb.
      rewrite transportf_set.
      {
        apply idpath.
      }
      apply setproperty.
    - intros.
      use lin_dep_assembly_morphism_eq.
      intros.
      refine (_ @ pathsinv0 (transportb_lin_dep_assembly_mor _ _ _)).
      apply pathsinv0.
      unfold transportb.
      rewrite transportf_set.
      {
        apply idpath.
      }
      apply setproperty.
    - intros.
      apply isaset_lin_dep_assembly_morphism.
  Qed.
  
  Definition disp_cat_of_lin_dep_assembly
    : disp_cat (cat_of_assembly AC).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_of_lin_dep_assembly_data.
    - exact disp_cat_of_lin_dep_assembly_axioms.
  Defined.

  Definition fiber_comp_lin_dep_assembly_morphism
             {Γ : assembly AC}
             {X₁ X₂ X₃ : dep_assembly Γ}
             (f : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism _))
             (g : lin_dep_assembly_morphism X₂ X₃ (id_assembly_morphism _))
    : lin_dep_assembly_morphism X₁ X₃ (id_assembly_morphism _)
    := compose (C := disp_cat_of_lin_dep_assembly[{Γ}]) f g.

  Proposition fiber_comp_lin_dep_assembly
              {Γ : assembly AC}
              {X₁ X₂ X₃ : dep_assembly Γ}
              (f : disp_cat_of_lin_dep_assembly[{Γ}] ⟦ X₁ , X₂ ⟧)
              (g : disp_cat_of_lin_dep_assembly[{Γ}] ⟦ X₂ , X₃ ⟧)
              {x : Γ}
              (xx : X₁ x)
    : pr1 (f · g) x xx = pr1 g _ (pr1 f _ xx).
  Proof.
    cbn.
    etrans.
    {
      exact (transportf_lin_dep_assembly_mor
               (id_right _)
               (comp_lin_dep_assembly_morphism f g) xx).
    }
    rewrite transportf_set.
    {
      apply idpath.
    }
    apply setproperty.
  Qed.

  Proposition idtoiso_fiber_lin_dep_assembly
              {Γ : assembly AC}
              {X₁ X₂ : dep_assembly Γ}
              (p : X₁ = X₂)
              {x : Γ}
              (xx : X₁ x)
    : pr11 (idtoiso (C := disp_cat_of_lin_dep_assembly[{Γ}]) p) x xx
      =
      cast (maponpaths (λ z, pr11 z) (eqtohomot p x)) xx.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.
  
  (** * 4. The cleaving for linear dependent assemblies *)
  Section CartesianLift.
    Context {Γ₁ Γ₂ : assembly AC}
            (s : assembly_morphism Γ₁ Γ₂)
            (X : dep_assembly Γ₂).

    Definition lin_dep_assembly_subst
      : disp_cat_of_lin_dep_assembly Γ₁
      := λ x, X(s x).

    Proposition transportf_lin_dep_assembly_subst
                {x₁ x₂ : Γ₁}
                (p : x₁ = x₂)
                (xx : X (s x₁))
      : transportf lin_dep_assembly_subst p xx
        =
        transportf X (maponpaths s p) xx.
    Proof.
      induction p.
      apply idpath.
    Qed.

    Definition lin_dep_assembly_subst_mor
      : lin_dep_assembly_morphism lin_dep_assembly_subst X s.
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ x xx, xx).
      - abstract
          (use hinhpr ;
           refine (K* ,, _) ;
           intros x xx b₁ b₂ p₁ p₂ ;
           rewrite linear_combinatory_algebra_ks_eq ;
           exact p₂).
    Defined.

    Section Cartesian.
      Context {Δ : assembly AC}
              {s' : assembly_morphism Δ Γ₁}
              {X' : dep_assembly Δ}
              (f : lin_dep_assembly_morphism X' X (comp_assembly_morphism s' s)).

      Definition lin_dep_assembly_cartesian_factorisation
        : lin_dep_assembly_morphism X' lin_dep_assembly_subst s'.
      Proof.
        use make_lin_dep_assembly_morphism.
        - exact (λ x xx, f x xx).
        - exact (lin_dep_assembly_morphism_function_track f).
      Defined.

      Proposition lin_dep_assembly_cartesian_factorisation_comm
        : comp_lin_dep_assembly_morphism
            lin_dep_assembly_cartesian_factorisation
            lin_dep_assembly_subst_mor
          =
          f.
      Proof.
        use lin_dep_assembly_morphism_eq.
        intros x xx ; cbn.
        apply idpath.
      Qed.

      Proposition lin_dep_assembly_cartesian_factorisation_unique
        : isaprop
            (∑ g, comp_lin_dep_assembly_morphism g lin_dep_assembly_subst_mor = f).
      Proof.
        use invproofirrelevance.
        intros g₁ g₂.
        use subtypePath.
        {
          intro.
          apply isaset_lin_dep_assembly_morphism.
        }
        use lin_dep_assembly_morphism_eq.
        intros x xx ; cbn.
        exact (lin_dep_assembly_morphism_eq_point (pr2 g₁ @ pathsinv0 (pr2 g₂)) xx).
      Qed.
    End Cartesian.    

    Definition is_cartesian_lin_dep_assembly_subst_mor
      : is_cartesian
          (D := disp_cat_of_lin_dep_assembly)
          lin_dep_assembly_subst_mor.
    Proof.
      intros Δ s' X' f.
      use iscontraprop1.
      - apply lin_dep_assembly_cartesian_factorisation_unique.
      - refine (lin_dep_assembly_cartesian_factorisation f ,, _).
        apply lin_dep_assembly_cartesian_factorisation_comm.
    Defined.
  End CartesianLift.

  Arguments lin_dep_assembly_subst /.
  
  Definition lin_dep_assembly_cleaving
    : cleaving disp_cat_of_lin_dep_assembly.
  Proof.
    intros Γ₂ Γ₁ s X.
    simple refine (_ ,, _ ,, _).
    - exact (lin_dep_assembly_subst s X).
    - exact (lin_dep_assembly_subst_mor s X).
    - exact (is_cartesian_lin_dep_assembly_subst_mor s X).
  Defined.

  (** * 5. Some equational lemmas *)
  Proposition fiber_functor_from_cleaving_lin_dep_assembly
              {Γ₁ Γ₂ : assembly AC}
              (s : assembly_morphism Γ₁ Γ₂)
              {X₁ X₂ : dep_assembly Γ₂}
              (f : lin_dep_assembly_morphism X₁ X₂ (id_assembly_morphism Γ₂))
              {x : Γ₁}
              (xx : X₁(s x))
    : pr1 (#(fiber_functor_from_cleaving _ lin_dep_assembly_cleaving s) f) x xx
      =
      f (s x) xx.
  Proof.
    cbn.
    etrans.
    {
      exact (transportf_lin_dep_assembly_mor (id_right _ @ pathsinv0 (id_left _)) _ xx).
    }
    rewrite transportf_set.
    {
      apply idpath.
    }
    apply setproperty.
  Qed.

  Proposition fiber_functor_from_cleaving_identity_lin_dep_assembly
              {Γ : assembly AC}
              (X : dep_assembly Γ)
              {x : Γ}
              (xx : X x)
    : pr1 (fiber_functor_from_cleaving_identity lin_dep_assembly_cleaving Γ X) x xx
      =
      xx.
  Proof.
    cbn.
    refine (transportb_lin_dep_assembly_mor _ _ _ @ _).
    unfold transportb.
    refine (_ @ idpath_transportf X _).
    apply maponpaths_2.
    apply setproperty.
  Qed.

  Proposition fiber_functor_from_cleaving_comp_lin_dep_assembly
              {Γ₁ Γ₂ Γ₃ : assembly AC}
              (s₁ : assembly_morphism Γ₁ Γ₂)
              (s₂ : assembly_morphism Γ₂ Γ₃)
              {X : dep_assembly Γ₃}
              {x : Γ₁}
              (xx : X(s₂(s₁ x)))
    : pr1 (fiber_functor_from_cleaving_comp lin_dep_assembly_cleaving s₂ s₁ X) x xx
      =
      xx.
  Proof.
    cbn.
    refine (transportb_lin_dep_assembly_mor _ _ _ @ _).
    unfold transportb.
    refine (_ @ idpath_transportf X _).
    apply maponpaths_2.
    apply setproperty.
  Qed.

  Proposition eq_function_idtoiso_lin_dep_assembly
              {Γ₁ Γ₂ : assembly AC}
              (X : dep_assembly Γ₂)
              {s₁ s₂ : assembly_morphism Γ₁ Γ₂}
              (p : s₁ = s₂)
              {x : Γ₁}
              (xx : X (s₁ x))
    : pr11 (idtoiso
              (C := disp_cat_of_lin_dep_assembly[{Γ₁}])
              (maponpaths (λ (f : assembly_morphism Γ₁ Γ₂) (z : Γ₁), X (f z)) p))
        x
        xx
      =
      transportf X (assembly_morphism_eq_point p x) xx.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition comm_nat_z_iso_lin_dep_assembly
              {Γ₁ Γ₂ Γ₃ Γ₄ : assembly AC}
              {f : assembly_morphism Γ₂ Γ₁}
              {g : assembly_morphism Γ₃ Γ₁}
              {h : assembly_morphism Γ₄ Γ₃}
              {k : assembly_morphism Γ₄ Γ₂}
              (p : comp_assembly_morphism k f = comp_assembly_morphism h g)
              {X : dep_assembly Γ₁}
              {x : Γ₄}
              (xx : X(f(k x)))
    : pr1 (comm_nat_z_iso lin_dep_assembly_cleaving _ _ _ _ p X) x xx
      =
      transportf X (assembly_morphism_eq_point p x) xx.
  Proof.
    cbn.
    etrans.
    {
      use transportf_lin_dep_assembly_mor.
    }
    simpl.
    etrans.
    {
      apply maponpaths.
      use transportf_lin_dep_assembly_mor.
    }
    simpl.
    etrans.
    {
      do 2 apply maponpaths.
      use transportf_lin_dep_assembly_mor.
    }
    unfold transportb ; simpl.
    etrans.
    {
      do 4 apply maponpaths.
      use transportf_lin_dep_assembly_mor.
    }
    cbn.
    etrans.
    {
      do 3 apply maponpaths.
      use eq_function_idtoiso_lin_dep_assembly.
    }
    rewrite !(functtransportf (λ z, g(h z)) X).
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply setproperty.
  Qed.

  (** * 6. The fiberwise terminal object *)
  Section FiberwiseTerminal.
    Context (Γ : assembly AC).
    
    Definition terminal_lin_dep_assembly_morphism
               (X : dep_assembly Γ)
      : lin_dep_assembly_morphism
          X
          (terminal_dep_assembly Γ)
          (id_assembly_morphism Γ).
    Proof.
      use make_lin_dep_assembly_morphism.
      - exact (λ _ _, tt).
      - abstract
          (use hinhpr ;
           refine (I ,, _) ;
           unfold tracks_lin_dep_assembly_morphism ;
           intros ; cbn ;
           exact tt).
    Defined.
    
    Definition fiberwise_terminal_object_lin_dep_assembly
      : Terminal disp_cat_of_lin_dep_assembly[{Γ}].
    Proof.
      use make_Terminal.
      - exact (terminal_dep_assembly Γ).
      - intros X.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros f₁ f₂ ;
             use dep_assembly_morphism_eq ;
             intros x xx ;
             apply isapropunit).
        + exact (terminal_lin_dep_assembly_morphism X).
    Defined.
  End FiberwiseTerminal.

  Definition fiberwise_terminal_lin_dep_assembly
    : fiberwise_terminal lin_dep_assembly_cleaving.
  Proof.
    split.
    - exact fiberwise_terminal_object_lin_dep_assembly.
    - abstract
        (intros Γ₁ Γ₂ s ;
         use (preserves_terminal_if_preserves_chosen
                (fiberwise_terminal_object_lin_dep_assembly Γ₂)) ;
         apply fiberwise_terminal_object_lin_dep_assembly).
  Defined.
End DependentAssembly.

Arguments disp_cat_of_lin_dep_assembly_ob_mor : clear implicits.
Arguments disp_cat_of_lin_dep_assembly_id_comp : clear implicits.
Arguments disp_cat_of_lin_dep_assembly_data : clear implicits.
Arguments disp_cat_of_lin_dep_assembly_axioms : clear implicits.
Arguments disp_cat_of_lin_dep_assembly : clear implicits.
Arguments lin_dep_assembly_subst /.
Arguments lin_dep_assembly_cleaving : clear implicits.
Arguments fiberwise_terminal_lin_dep_assembly : clear implicits.
