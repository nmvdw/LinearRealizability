(**

 Modest sets

 Contents
 1. The category of modest sets
 2. Examples of modest sets
 2.1. The terminal assembly is modest
 2.2. The product of mdoest sets
 2.3. The equalizer of modest sets
 2.4. The pullback of modest sets
 2.5. The initial modest set
 2.6. The coproduct of modest sets
 2.7. The modest set of natural numbers
 2.8. Exponentials

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.

Local Open Scope ca.
Local Open Scope assembly.

(** 1. The category of modest sets *)
Definition is_modest
           {A : applicative_structure}
           (X : assembly A)
  : hProp
  := (∀ (a : A) (x₁ x₂ : X), a ⊩ x₁ ⇒ a ⊩ x₂ ⇒ x₁ = x₂)%logic.

Definition cat_of_modest_set
           (A : bi_algebra)
  : category
  := full_subcat (cat_of_assembly A) is_modest.

Definition modest_set
           (A : bi_algebra)
  : UU
  := cat_of_modest_set A.

Definition make_modest_set
           {A : bi_algebra}
           (X : assembly A)
           (HX : is_modest X)
  : modest_set A
  := X ,, HX.
           
Coercion modest_set_to_assembly
         {A : bi_algebra}
         (X : modest_set A)
  : assembly A
  := pr1 X.

Proposition is_modest_modest_set
            {A : bi_algebra}
            (X : modest_set A)
            {a : A}
            {x₁ x₂ : X}
            (p : a ⊩ x₁)
            (q : a ⊩ x₂)
  : x₁ = x₂.
Proof.
  exact (pr2 X a x₁ x₂ p q).
Defined.

Definition modest_set_morphism
           {A : bi_algebra}
           (X₁ X₂ : modest_set A)
  : UU
  := (X₁ --> X₂)%cat.

Definition make_modest_set_morphism
           {A : bi_algebra}
           {X₁ X₂ : modest_set A}
           (f : assembly_morphism X₁ X₂)
  : modest_set_morphism X₁ X₂
  := f ,, tt.

Coercion modest_set_to_assembly_morphism
         {A : bi_algebra}
         {X₁ X₂ : modest_set A}
         (f : modest_set_morphism X₁ X₂)
  : assembly_morphism X₁ X₂
  := pr1 f.

Proposition eq_modest_set_morphism
            {A : bi_algebra}
            {X₁ X₂ : modest_set A}
            {f g : modest_set_morphism X₁ X₂}
            (p : ∏ (x : X₁), f x = g x)
  : f = g.
Proof.
  use subtypePath.
  {
    intro.
    apply isapropunit.
  }
  use assembly_morphism_eq.
  exact p.
Qed.

Proposition eq_modest_set_morphism_point
            {A : bi_algebra}
            {X₁ X₂ : modest_set A}
            {f g : modest_set_morphism X₁ X₂}
            (p : f = g)
            (x : X₁)
  : f x = g x.
Proof.
  induction p.
  apply idpath.
Qed.

(** * 2. Examples of modest sets *)

(** ** 2.1. The terminal assembly is modest *)
Proposition is_modest_terminal_assembly
            (A : combinatory_algebra)
  : is_modest (terminal_assembly A).
Proof.
  intros a x₁ x₂ p q.
  apply isapropunit.
Qed.

(** ** 2.2. The product of mdoest sets *)
Proposition is_modest_prod
            {A : combinatory_algebra}
            {X₁ X₂ : assembly A}
            (HX₁ : is_modest X₁)
            (HX₂ : is_modest X₂)
  : is_modest (prod_assembly X₁ X₂).
Proof.
  intros a xy₁ xy₂ p q.
  use pathsdirprod.
  - use (HX₁ (π₁ · a)).
    + exact (pr1 p).
    + exact (pr1 q).
  - use (HX₂ (π₂ · a)).
    + exact (pr2 p).
    + exact (pr2 q).
Qed.

(** ** 2.3. The equalizer of modest sets *)
Proposition is_modest_equalizer
            {A : combinatory_algebra}
            {X₁ X₂ : assembly A}
            (φ ψ : assembly_morphism X₁ X₂)
            (HX₁ : is_modest X₁)
  : is_modest (equalizer_assembly φ ψ).
Proof.
  intros a x₁ x₂ p q.
  use subtypePath.
  {
    intro.
    apply setproperty.
  }
  use (HX₁ a).
  - exact p.
  - exact q.
Qed.

(** ** 2.4. The pullback of modest sets *)
Proposition is_modest_pullback
            {A : combinatory_algebra}
            {X₁ X₂ X₃ : assembly A}
            (f : assembly_morphism X₁ X₃)
            (g : assembly_morphism X₂ X₃)
            (HX₁ : is_modest X₁)
            (HX₂ : is_modest X₂)
  : is_modest (pullback_assembly f g).
Proof.
  intros a x₁ x₂ p q.
  use pullback_assembly_eq.
  - exact (HX₁ _ _ _ (pr1 p) (pr1 q)).
  - exact (HX₂ _ _ _ (pr2 p) (pr2 q)).
Qed.

(** ** 2.5. The initial modest set *)
Proposition is_modest_initial_assembly
            (A : combinatory_algebra)
  : is_modest (initial_assembly A).
Proof.
  intros a x.
  induction x.
Qed.

(** ** 2.6. The coproduct of modest sets *)
Proposition is_modest_sum_assembly
            {A : combinatory_algebra}
            (HA : is_non_trivial A)
            {X₁ X₂ : assembly A}
            (HX₁ : is_modest X₁)
            (HX₂ : is_modest X₂)
  : is_modest (sum_assembly X₁ X₂).
Proof.
  intros a x₁ x₂.
  use factor_through_squash_hProp.
  intros p₁.
  use factor_through_squash_hProp.
  intros p₂.
  induction p₁ as [ [ p₁ r₁ ] | [ q₁ r₁ ] ], p₂ as [ [ p₂ r₂ ] | [ q₂ r₂ ] ].
  - revert r₁.
    use factor_through_squash_hProp.
    intros ( y₁ & r₁ & Hy₁ ).
    revert r₂.
    use factor_through_squash_hProp.
    intros ( y₂ & r₂ & Hy₂ ).
    rewrite Hy₁, Hy₂.
    apply maponpaths.
    use (HX₁ (π₂ · a)).
    + exact r₁.
    + exact r₂.
  - apply fromempty.
    use (is_non_trivial_k_ks HA).
    rewrite <- p₁, <- q₂.
    apply idpath.
  - apply fromempty.
    use (is_non_trivial_k_ks HA).
    rewrite <- q₁, <- p₂.
    apply idpath.
  - revert r₁.
    use factor_through_squash_hProp.
    intros ( y₁ & r₁ & Hy₁ ).
    revert r₂.
    use factor_through_squash_hProp.
    intros ( y₂ & r₂ & Hy₂ ).
    rewrite Hy₁, Hy₂.
    apply maponpaths.
    use (HX₂ (π₂ · a)).
    + exact r₁.
    + exact r₂.
Qed.

(** ** 2.7. The modest set of natural numbers *)
Definition is_modest_nat_assembly
           {A : combinatory_algebra}
           (HA : is_non_trivial A)
  : is_modest (nat_assembly A).
Proof.
  intros a n₁ ; revert a.
  induction n₁ as [ | n₁ IHn₁ ] ; intro a.
  - intros n₂.
    destruct n₂ as [ | n₂ ] ; intros p q.
    + reflexivity.
    + apply fromempty.
      simpl in p, q.
      use (combinatory_algebra_nat_Z_succ_neq HA n₂).
      refine (_ @ q).
      exact (!p).
  - intros n₂.
    destruct n₂ as [ | n₂ ] ; intros p q.
    + apply fromempty.
      simpl in p, q.
      use (combinatory_algebra_nat_Z_succ_neq HA n₁).
      exact (!q @ p).
    + apply maponpaths.
      use IHn₁.
      * exact (π₂ · a).
      * simpl in p.
        rewrite p.
        rewrite combinatory_algebra_pr2_pair.
        apply idpath.
      * rewrite q.
        simpl.
        rewrite combinatory_algebra_pr2_pair.
        apply idpath.
Qed.

(** * 2.8. Exponentials *)
Definition is_modest_function_assembly
           {A : combinatory_algebra}
           {X₁ X₂ : assembly A}
           (HX₂ : is_modest X₂)
  : is_modest (function_assembly X₁ X₂).
Proof.
  intros a f₁ f₂ p₁ p₂.
  use assembly_morphism_eq.
  intro x.
  pose proof (assembly_realizes_el x) as q.
  revert q.
  use factor_through_squash.
  {
    apply setproperty.
  }
  intros ( b & q ).
  use HX₂.
  - exact (a · b).
  - use p₁.
    exact q.
  - use p₂.
    exact q.
Qed.
