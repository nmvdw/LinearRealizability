(**

 Connectives for formulas in the realizability model

 In this file, we give concrete descriptions of each of the formulas in the linear
 realizability model. Note that we only give descriptions for the connectives, and
 that in other files we prove they satisfy the desired rules. We also look at the
 membership formula since the realizability model supports higher order logic.

 Content
 1. Cartesian connectives
 1.1. Truth formula: ⊤
 1.2. Falsity formula: ⊥
 1.3. Conjunction: ∧
 1.4. Disjunction: ∨
 1.5. Implication: ⇒
 1.6. Universal quantification: ∀
 1.7. Existential quantification: ∃
 1.8. Equality: ≡
 1.9. Membership: ∈
 2. Linear connectives
 2.1. Unit for additive conjunction: top
 2.2. Unit for additive disjunction: bot
 2.3. Multiplicative unit: 1
 2.4. The tensor: ⊗
 2.5. Linear implication: ⊸
 2.6. Additive conjunction: &
 2.7. Additive disjunction: +
 2.8. Multiplication: M (from linear propositions to Cartesian ones)
 2.9. Linearization: L (from Cartesian propositions to linear ones)
 2.10. Linear universal quantification: ⊓
 2.11. Linear existential: ⊏

 Appendix
 From these concrete descriptions we can immediately see when a formula is satisfied
 in the model, and we shall give these descriptions below. Recall that a formula `t` in
 context `Γ : assembly A` is determined by a relation between `Γ` and `A`. We say
 that `a ⊫_{x} t` if `t` relates `a` and `x`. This relation is determined by the following
 clauses.

 <<
 Cartesian connectives
 NOTE:
   The operations below assume that we are working with some *combinatory algebra* A.
   In case A is a linear combinatory algebra, then ! needs to be added at the appropriate
   places, because `a · b` in the combinatory algebra `A_!` is defined to be `a · !b`.

      a ⊫_{x} ⊤        always

      a ⊫_{x} ⊥        never

      a ⊫_{x} t₁ ∧ t₂
        iff
      π₁ · a ⊫_{x} t₁   and   π₂ · a ⊫_{x} t₂

      a ⊫_{x} t₁ ∨ t₂
        iff
      K = π₁ · a   and   π₂ · a ⊫_{x} t₁
        or
      K* = π₁ · a   and   π₂ · a ⊫_{x} t₂

      a ⊫ t₁ ⇒ t₂
        iff
      for all b : A: if b ⊫_{x} t₁  then  a · b ⊫_{x} t₂

      a ⊫_{x} ∀ (y : X) t
        iff
      for all y : X and b : A: if b ⊩ y  then  a · b ⊫_{x ,, y} t

      a ⊫_{x} ∃ (y : X) t
        iff
      there is y : X such that  π₁ · a ⊩ y  and  π₂ · a ⊫_{x ,, y} t

      a ⊫_{x} f ≡ g
        iff
      f = g

      a ⊫_{x ,, t} x ∈ t
        iff
      t x a

 Linear connectives

      a ⊫_{x} top        always

      a ⊫_{x} bot        never

      a ⊫_{x} 1
        iff
      a = I

      a ⊫_{x} t₁ ⊗ t₂
        iff
      there exists b₁, b₂ : A such that
        a = lin_pair · b₁ · b₂
        b₁ ⊫_{x} t₁
        b₂ ⊫_{x} t₂

      a ⊫_{x} t₁ ⊸ t₂
        iff
      for all b : A: if b ⊫_{x} t₁  then  a · b ⊫_{x} t₂

      a ⊫_{x} t₁ & t₂
        iff
      there are b c₁ c₂ : A such that
        a = lin_pair · b · (lin_pair · (!c₁) · (!c₂))
        c₁ · b ⊫_{x} t₁
        c₂ · b ⊫_{x} t₂

      a ⊫_{x} t₁ + t₂
        iff
      there is b : A such that
          a = lin_pair · lca_bincoprod_left · b  and b ⊫_{x} t₁
        or
          a = lin_pair · lca_bincoprod_right · b  and b ⊫_{x} t₂

      a ⊫_{x} M t
        iff
      a ⊫_{x} t

      a ⊫_{x} L t
        iff
      there is b : A such that
        a = !b
        b ⊫_{x} t

      a ⊫_{x} ⊓ (y : X) t
        iff
      for all y : X and b : A such that b ⊩ y, we have a · !b ⊫_{x ,, y} t

      a ⊫_{x} ⊏ (y : X) t
        iff
      there are y : X and b c : A such that
        a = lin_pair · (!b) · c
        b ⊩ y
        c ⊫_{x ,, y} t
 >>

 To understand membership `∈`, note the following:
 - The powerset of an assembly `Γ` is the function space from `Γ` to `Prop`.
 - Hence, terms of the powerset are literally the same as formulas.
 - For membership, we work in a context with `x : Γ` and `t` in the powerset.

 For the tensor `⊗`, recall that `lin_pair` is defined as the λ-term
     `λ x λ y λ z. z x y`

 For the additive disjunction `+`, we use the combinators `lca_bincoprod_left`
 and `lca_bincoprod_right`. These satisfy the following equations:
 ```
 lca_bincoprod_left · (!a₂) · b₁ · (!a₁) · b₂ = a₁ · b₁ · b₂
 lca_bincoprod_right · (!a₂) · b₁ · (!a₁) · b₂ = a₂ · b₁ · b₂
 ```

 We can also interpret equality as a linear connective, and then we get the
 same concrete description as for the Cartesian case. The same can be said
 for membership.

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Combinators.
Require Import Basics.BIAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.LinearAssembly.
Require Import Types.Terms.
Require Import Types.Prop.
Require Import Logic.Formulas.

Local Open Scope ca.
Local Open Scope assembly.
Local Open Scope logic.

(** * 1. Cartesian connectives *)
Section CartesianConnectives.
  Context {A : combinatory_algebra}.

  (** ** 1.1. Truth formula: ⊤ *)
  Definition assembly_truth_prop
             (Γ : assembly A)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, htrue).
  Defined.

  (** ** 1.2. Falsity formula: ⊥ *)
  Definition assembly_false_prop
             (Γ : assembly A)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, hfalse).
  Defined.

  (** ** 1.3. Conjunction: ∧ *)
  Definition assembly_conj_prop
             {Γ : assembly A}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, t₁ x (π₁ · a) ∧ t₂ x (π₂ · a)).
  Defined.

  (** ** 1.4. Disjunction: ∨ *)
  Definition assembly_disj_prop
             {Γ : assembly A}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a,
           ((K = π₁ · a) ∧ t₁ x (π₂ · a))
           ∨
           ((K* = π₁ · a) ∧ t₂ x (π₂ · a))).
  Defined.

  (** ** 1.5. Implication: ⇒ *)
  Definition assembly_impl_prop
             {Γ : assembly A}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∀ (b : A), (t₁ x b : hProp) ⇒ t₂ x (a · b)).
  Defined.

  (** ** 1.6. Universal quantification: ∀ *)
  Definition assembly_forall_prop
             {Γ : assembly A}
             (X : assembly A)
             (t : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∀ (y : X) (b : A), b ⊩ y ⇒ t (x ,, y) (a · b)).
  Defined.

  (** ** 1.7. Existential quantification: ∃ *)
  Definition assembly_exists_prop
             {Γ : assembly A}
             (X : assembly A)
             (t : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∃ (y : X), (π₁ · a ⊩ y) ∧ t (x ,, y) (π₂ · a)).
  Defined.

  (** ** 1.8. Equality: ≡ *)
  (**
     Note that the following formula is needed to get equality as a left adjoint.
   *)
  Definition assembly_equality_prop
             {Γ : assembly A}
             (t : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type (prod_assembly Γ Γ)).
  Proof.
    use make_assembly_prop.
    exact (λ xy a, pr1 xy = pr2 xy ∧ t (pr1 xy) a).
  Defined.

  Definition assembly_eq_prop
             {Γ X : assembly A}
             (t₁ t₂ : assembly_morphism Γ X)
    : assembly_term (assembly_prop_universe_type Γ)
    := subst_assembly_term
         (pair_assembly_morphism t₁ t₂)
         (assembly_equality_prop (assembly_truth_prop X)).

  (** ** 1.9. Membership: ∈ *)
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
End CartesianConnectives.

Local Close Scope ca.
Local Open Scope lca.

(** * 2. Linear connectives *)
Section LinearConnectives.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  (** * 2.1. Unit for additive conjunction: top *)
  Definition assembly_truth_lin_prop
             (Γ : assembly AC)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, htrue).
  Defined.

  (** ** 2.2. Unit for additive disjunction: bot *)
  Definition assembly_false_lin_prop
             (Γ : assembly AC)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, hfalse).
  Defined.

  (** ** 2.3. Multiplicative unit: 1 *)
  Definition assembly_unit_lin_prop
             (Γ : assembly AC)
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, a = I).
  Defined.

  (** ** 2.4. The tensor: ⊗ *)
  Definition assembly_tensor_lin_prop
             {Γ : assembly AC}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∃ (b₁ b₂ : A), (a = lin_pair · b₁ · b₂) ∧ t₁ x b₁ ∧ t₂ x b₂).
  Defined.    

  (** ** 2.5. Linear implication: ⊸ *)
  Definition assembly_impl_lin_prop
             {Γ : assembly AC}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x (a : A), ∀ (b : A), (t₁ x b : hProp) ⇒ t₂ x (a · b)).
  Defined.

  (** ** 2.6. Additive conjunction: & *)
  Definition assembly_conj_lin_prop
             {Γ : assembly AC}
             (t₁ t₂ : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ (x : Γ) (a : A),
           ∃ (b c₁ c₂ : A),
           (a = lin_pair · b · (lin_pair · (!c₁) · (!c₂)))
           ∧ t₁ x (c₁ · b)
           ∧ t₂ x (c₂ · b)).
  Defined.

  (** ** 2.7. Additive disjunction: + *)
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

  (** ** 2.8. Multiplication: M (from linear propositions to Cartesian ones) *)
  Definition assembly_lin_prop_to_prop
             {Γ : assembly AC}
             (t : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ)
    := t.

  (** ** 2.9. Linearization: L (from Cartesian propositions to linear ones) *)
  Definition assembly_prop_to_lin_prop
             {Γ : assembly AC}
             (t : assembly_term (assembly_prop_universe_type Γ))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ (x : Γ) (a : A), ∃ (b : A), (a = !b) ∧ t x b).
  Defined.

  (** ** 2.10. Linear universal quantification: ⊓ *)
  Definition assembly_forall_lin_prop
             {Γ X : assembly AC}
             (t : assembly_term (assembly_prop_universe_type (prod_assembly Γ X)))
    : assembly_term (assembly_prop_universe_type Γ).
  Proof.
    use make_assembly_prop.
    exact (λ x a, ∀ (y : X) (b : A), b ⊩ y ⇒ t (x ,, y) (a · b)).
  Defined.

  (** ** 2.11. Linear existential: ⊏ *)
  Definition assembly_exists_lin_prop
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
End LinearConnectives.

Notation "'⊤'" := (assembly_truth_prop _) : assembly.
Notation "'⊥'" := (assembly_false_prop _) : assembly.
Notation "t₁ ∧ t₂" := (assembly_conj_prop t₁ t₂) : assembly.
Notation "t₁ ∨ t₂" := (assembly_conj_prop t₁ t₂) : assembly.
Notation "t₁ ⇒ t₂" := (assembly_conj_prop t₁ t₂) : assembly.
Notation "∀a t" := (assembly_forall_prop t) (at level 10) : assembly.
Notation "∃a t" := (assembly_exists_prop t) (at level 10) : assembly.
Notation "t₁ ≡ t₂ " := (assembly_eq_prop t₁ t₂) : assembly.
Notation "'top'" := (assembly_truth_lin_prop _) : assembly.
Notation "'bot'" := (assembly_false_lin_prop _) : assembly.
Notation "'𝟙'" := (assembly_unit_lin_prop _) : assembly. (* \b1 *)
Notation "t₁ ⊗ t₂" := (assembly_tensor_lin_prop t₁ t₂) : assembly. (* \otimes *)
Notation "t₁ ⊸ t₂" := (assembly_tensor_lin_prop t₁ t₂) (at level 45, right associativity)
    : assembly. (* \-o *)
Notation "t₁ & t₂" := (assembly_conj_lin_prop t₁ t₂) (at level 80, right associativity)
    : assembly.
Notation "t₁ + t₂" := (assembly_disj_lin_prop t₁ t₂) : assembly.
Notation "'M'" := assembly_lin_prop_to_prop : assembly.
Notation "'L'" := assembly_prop_to_lin_prop : assembly.
Notation "⊓a t" := (assembly_forall_lin_prop t) (at level 10) : assembly.
Notation "⊏a t" := (assembly_exists_lin_prop t) (at level 10) : assembly.
