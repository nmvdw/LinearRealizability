(**

 Terms in the comprehension category of assemblies

 Contents
 1. Definition of terms
 2. Equivalence with sections

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Require Import SetFamilies.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.DependentAssembly.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope cat.

Section TermsAssemblies.
  Context {A : combinatory_algebra}
          {Γ : assembly A}
          (X : dep_assembly Γ).

  (** * 1. Definition of terms *)
  Definition assembly_term
    : UU
    := ∑ (t : section_set_fam X),
       ∃ (a : A), ∏ (b : A) (x : Γ), b ⊩ x → (a · b)%ca ⊩ t x.

  Definition make_assembly_term
             (t : ∏ (x : Γ), X x)
             (H : ∃ (a : A), ∏ (b : A) (x : Γ), b ⊩ x → (a · b)%ca ⊩ t x)
    : assembly_term
    := t ,, H.
  
  Definition assembly_term_to_function
             (t : assembly_term)
             (x : Γ)
    : X x
    := pr1 t x.

  Coercion assembly_term_to_function : assembly_term >-> Funclass.

  Proposition assembly_term_tracker
              (t : assembly_term)
    :  ∃ (a : A), ∏ (b : A) (x : Γ), b ⊩ x → (a · b)%ca ⊩ t x.
  Proof.
    exact (pr2 t).
  Defined.

  Proposition assembly_term_eq
              {t₁ t₂ : assembly_term}
              (p : ∏ (x : Γ), t₁ x = t₂ x)
    : t₁ = t₂.
  Proof.
    use subtypePath_prop.
    use funextsec.
    exact p.
  Qed.

  (** * 2. Equivalence with sections *)
  Section TermToSection.
    Context (t : assembly_term).

    Definition assembly_term_to_section_mor
      : assembly_morphism Γ (total_assembly X).
    Proof.
      use make_assembly_morphism.
      - exact (λ x, x ,, t x).
      - abstract
          (pose proof (q := assembly_term_tracker t) ;
           revert q ;
           use factor_through_squash_hProp ;
           intros ( a & p ) ;
           use hinhpr ;
           refine (tm_t · a ,, _)%ca ;
           intros b x q ;
           rewrite combinatory_algebra_tm_fun_eq ;
           simpl ;
           rewrite combinatory_algebra_pr1_pair ;
           rewrite combinatory_algebra_pr2_pair ;
           refine (q ,, _) ;
           use p ;
           exact q).
    Defined.
    
    Definition assembly_term_to_section                 
      : section_of_mor
          (C := cat_of_assembly A)
          (total_assembly_pr X).
    Proof.
      use make_section_of_mor.
      - exact assembly_term_to_section_mor.
      - abstract
          (use assembly_morphism_eq ;
           intros x ; cbn ;
           apply idpath).
    Defined.
  End TermToSection.

  Section SectionToTerm.
    Context (t : section_of_mor
                   (C := cat_of_assembly A)
                   (total_assembly_pr X)).

    Let f : assembly_morphism Γ (total_assembly X)
      := section_of_mor_to_mor t.
    
    Definition section_to_assembly_term
      : assembly_term.
    Proof.
      use make_assembly_term.
      - exact (λ x, transportf
                      X
                      (assembly_morphism_eq_point (section_of_mor_eq t) x)
                      (pr2 (f x))).
      - abstract
          (pose proof (assembly_morphism_tracked f) as q ;
           revert q ;
           use factor_through_squash_hProp ;
           intros ( a & p ) ;
           use hinhpr ;
           refine (B · π₂ · a ,, _)%ca ;
           intros b x q ;
           use dep_assembly_transportf_realizes ;
           rewrite combinatory_algebra_b_eq ;
           specialize (p b x q) ;
           exact (pr2 p)).
    Defined.
  End SectionToTerm.

  Definition assembly_term_weq_section
    : assembly_term
      ≃
      section_of_mor
        (C := cat_of_assembly A)
        (total_assembly_pr X).
  Proof.
    use weq_iso.
    - exact assembly_term_to_section.
    - exact section_to_assembly_term.
    - abstract
        (intro t ;
         use assembly_term_eq ;
         intro x ; cbn ;
         rewrite transportf_set ;
         [ apply idpath | ] ;
         apply setproperty).
    - abstract
        (intro t ;
         use eq_section_of_mor ;
         use assembly_morphism_eq ;
         intro x ; cbn ;
         use total2_paths_f ;
         [ exact (!(assembly_morphism_eq_point (section_of_mor_eq t) x)) | ] ;
         simpl ;
         rewrite transport_f_f ;
         rewrite transportf_set ; [ apply idpath | ] ;
         apply setproperty).
  Defined.
End TermsAssemblies.
