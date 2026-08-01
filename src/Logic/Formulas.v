(**

 Formulas

 Our goal is to study the logic in the linear realizability model. Specifically, our goal
 is to give concrete descriptions for the logical connectives of the type `Prop`. To do so,
 we first define two displayed categories over the categories of assemblies. One displayed
 category is defined for all combinatory algebras for which we shall interpret the usual
 connectives in first-order logic. The other displayed category is defined for all linear
 combinatory algebras, and for that one we shall interpret the connectives in linear logic.

 The objects of these displayed categories are terms of type `Prop`. Such terms are formulas
 in the realizability model. The morphisms in these displayed categories represent proofs,
 and they are morphisms between the associated types. It is important to note that the
 aforementioned displayed categories have different morphisms despite the fact that their
 objects are the same. The difference comes from the fact that to interpret linear logic, we
 use morphisms of linear assemblies.

 Content
 1. The displayed category of terms in `Prop` and ordinary morphisms
 2. A cleaving for this displayed category
 3. Useful functions to construct morphisms
 4. The displayed category of terms of `Prop` with linear morphisms
 5. A cleaving for this displayed category
 6. Useful functions to construct linear morphisms

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Types.Terms.
Require Import Types.Prop.

Local Open Scope ca.
Local Open Scope assembly.

Section CartesianFormulas.
  Context (A : combinatory_algebra).

  (** * 1. The displayed category of terms in `Prop` and ordinary morphisms *)
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

  (** * 2. A cleaving for this displayed category *)
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
                  → (t₂ x (a · b₁ · b₂) : hProp))
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
      exact ((a · b₁ · b₂) ,, p x b₁ b₂ q₁ q₂).
    - use hinhpr.
      refine (a ,, _).
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
      → (t₂ x (a · b₁ · b₂) : hProp).
  Proof.
    pose proof (dep_assembly_morphism_function_track φ) as p.
    revert p.
    use factor_through_squash_hProp.
    intros ( a & p ).
    use hinhpr.
    refine (a ,, _).
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
End CartesianFormulas.

Arguments cleaving_assembly_prop_disp_cat_mor {A Γ Δ} s t.
Arguments make_assembly_prop_proof {A Γ t₁ t₂} a p.
Arguments assembly_prop_to_proof {A Γ t₁ t₂} φ.
Arguments make_assembly_prop {A Γ} t.

Local Close Scope ca.
Local Open Scope lca.

Section LinearFormulas.
  Context (A : linear_combinatory_algebra).

  Let AC : combinatory_algebra := lca_to_ca A.

  (** * 4. The displayed category of terms of `Prop` with linear morphisms *)
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

  (** * 5. A cleaving for this displayed category *)
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
         refine (K* ,, _) ;
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

  (** * 6. Useful functions to construct linear morphisms *)
  Definition make_assembly_lin_prop_proof
             {Γ : assembly AC}
             {t₁ t₂ : assembly_term (assembly_prop_universe_type Γ)}
             (a : A)
             (p : ∏ (x : Γ)
                    (b₁ b₂ : A),
                  (b₁ ⊩ x)
                  → (t₁ x b₂ : hProp)
                  → (t₂ x (a · (!b₁) · b₂) : hProp))
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
      exact ((a · (!b₁) · b₂) ,, p x b₁ b₂ q₁ q₂).
    - use hinhpr.
      refine (a ,, _).
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
      → (t₂ x (a · (!b₁) · b₂) : hProp).
  Proof.
    pose proof (lin_dep_assembly_morphism_function_track φ) as p.
    revert p.
    use factor_through_squash_hProp.
    intros ( a & p ).
    use hinhpr.
    refine (a ,, _).
    intros x b₁ b₂ q₁ q₂.
    exact (p x (hinhpr (b₂ ,, q₂)) b₁ b₂ q₁ q₂).
  Qed.
End LinearFormulas.

Arguments cleaving_assembly_lin_prop_disp_cat_mor {A Γ Δ} s t.
Arguments make_assembly_lin_prop_proof {A Γ t₁ t₂} a p.
Arguments assembly_lin_prop_to_proof {A Γ t₁ t₂} φ.
