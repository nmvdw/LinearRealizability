(**

 The category of assemblies

 Contents
 1. Assemblies
 2. Morphisms of assemblies
 3. The identity morphism
 4. The composition of morphisms
 5. The category of assemblies

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.

Local Open Scope bi.

Declare Scope assembly.
Local Open Scope assembly.

(** * 1. Assemblies *)
Definition assembly
           (A : applicative_structure)
  : UU
  := ∑ (X : hSet)
       (R : A → X → hProp),
     ∏ (x : X), ∃ (a : A), R a x.

Definition make_assembly
           {A : applicative_structure}
           (X : hSet)
           (R : A → X → UU)
           (HR : ∏ (a : A) (x : X), isaprop (R a x))
           (e : ∏ (x : X), ∃ (a : A), R a x)
  : assembly A
  := X ,, (λ a x, make_hProp (R a x) (HR a x)) ,, e.

Definition make_assembly'
           {A : applicative_structure}
           (X : hSet)
           (R : A → X → hProp)
           (e : ∏ (x : X), ∃ (a : A), R a x)
  : assembly A
  := X ,, R ,, e.

Coercion set_of_assembly
         {A : applicative_structure}
         (X : assembly A)
  : hSet
  := pr1 X.

Definition assembly_realizes
           {A : applicative_structure}
           {X : assembly A}
           (a : A)
           (x : X)
  : hProp
  := pr12 X a x.

Notation "a ⊩ x" := (assembly_realizes a x) (at level 50) : assembly.

Proposition assembly_realizes_el
            {A : applicative_structure}
            {X : assembly A}
            (x : X)
  : ∃ (a : A), a ⊩ x.
Proof.
  exact (pr22 X x).
Defined.

(** * 2. Morphisms of assemblies *)
Definition tracks_morphism
           {A : applicative_structure}
           {X₁ X₂ : assembly A}
           (a : A)
           (f : X₁ → X₂)
  : hProp
  := (∀ (b : A) (x : X₁), b ⊩ x ⇒ a · b ⊩ f x)%logic.
           
Definition assembly_morphism
           {A : applicative_structure}
           (X₁ X₂ : assembly A)
  : UU
  := ∑ (f : X₁ → X₂),
     ∃ (a : A), tracks_morphism a f.

Proposition isaset_assembly_morphism
            {A : applicative_structure}
            (X₁ X₂ : assembly A)
  : isaset (assembly_morphism X₁ X₂).
Proof.
  use isaset_total2.
  - use funspace_isaset.
    apply setproperty.
  - intros.
    apply isasetaprop.
    do 2 (use impred ; intro).
    apply propproperty.
Qed.

Definition make_assembly_morphism
           {A : applicative_structure}
           {X₁ X₂ : assembly A}
           (f : X₁ → X₂)
           (p : ∃ (a : A), tracks_morphism a f)
  : assembly_morphism X₁ X₂
  := f ,, p.
           
Definition assembly_morphism_function
           {A : applicative_structure}
           {X₁ X₂ : assembly A}
           (f : assembly_morphism X₁ X₂)
           (x : X₁)
  : X₂
  := pr1 f x.

Coercion assembly_morphism_function : assembly_morphism >-> Funclass.

Proposition assembly_morphism_tracked
            {A : applicative_structure}
            {X₁ X₂ : assembly A}
            (f : assembly_morphism X₁ X₂)
  : ∃ (a : A), tracks_morphism a f.
Proof.
  exact (pr2 f).
Defined.

Proposition assembly_morphism_eq
            {A : applicative_structure}
            {X₁ X₂ : assembly A}
            {f g : assembly_morphism X₁ X₂}
            (p : ∏ (x : X₁), f x = g x)
  : f = g.
Proof.
  use subtypePath_prop.
  use funextsec.
  exact p.
Qed.

Proposition assembly_morphism_eq_point
            {A : applicative_structure}
            {X₁ X₂ : assembly A}
            {f g : assembly_morphism X₁ X₂}
            (p : f = g)
            (x : X₁)
  : f x = g x.
Proof.
  induction p.
  apply idpath.
Defined.

(** * 3. The identity morphism *)
Proposition id_assembly_morphism_tracks
            {A : bi_algebra}
            (X : assembly A)
  : ∃ (a : A), tracks_morphism a (λ (x : X), x).
Proof.
  use hinhpr.
  refine (I ,, _).
  intros a x p.
  rewrite bi_algebra_i_eq.
  exact p.
Qed.

Definition id_assembly_morphism_bi
           {A : bi_algebra}
           (X : assembly A)
  : assembly_morphism X X.
Proof.
  use make_assembly_morphism.
  - exact (λ x, x).
  - exact (id_assembly_morphism_tracks X).
Defined.

Definition id_assembly_morphism
           {A : combinatory_algebra}
           (X : assembly A)
  : assembly_morphism X X
  := id_assembly_morphism_bi (A := A) X.

(** * 4. The composition of morphisms *)
Proposition comp_assembly_morphism_tracks
            {A : bi_algebra}
            {X₁ X₂ X₃ : assembly A}
            (f : assembly_morphism X₁ X₂)
            (g : assembly_morphism X₂ X₃)
  : ∃ (a : A), tracks_morphism a (λ (x : X₁), g (f x)).
Proof.
  pose proof (assembly_morphism_tracked f) as p.
  revert p.
  use factor_through_squash_hProp.
  intros [ a₁ Ha₁ ].
  pose proof (assembly_morphism_tracked g) as p.
  revert p.
  use factor_through_squash_hProp.
  intros [ a₂ Ha₂ ].
  use hinhpr.
  refine (B · a₂ · a₁ ,, _).
  intros b x p.
  rewrite bi_algebra_b_eq.
  apply (Ha₂ (a₁ · b) (f x)).
  apply (Ha₁ b x).
  exact p.
Qed.

Definition comp_assembly_morphism_bi
           {A : bi_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism X₁ X₂)
           (g : assembly_morphism X₂ X₃)
  : assembly_morphism X₁ X₃.
Proof.
  use make_assembly_morphism.
  - exact (λ x, g(f x)).
  - exact (comp_assembly_morphism_tracks f g).
Defined.

Definition comp_assembly_morphism
           {A : combinatory_algebra}
           {X₁ X₂ X₃ : assembly A}
           (f : assembly_morphism X₁ X₂)
           (g : assembly_morphism X₂ X₃)
  : assembly_morphism X₁ X₃
  := comp_assembly_morphism_bi (A := A) f g.

(** * 5. The category of assemblies *)
Section CatOfAssemblies.
  Context (A : bi_algebra).

  Definition precat_ob_mor_of_assembly
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (assembly A).
    - exact assembly_morphism.
  Defined.

  Definition precat_data_of_assembly
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact precat_ob_mor_of_assembly.
    - exact id_assembly_morphism_bi.
    - exact (λ (X₁ X₂ X₃ : assembly A)
               (f : assembly_morphism X₁ X₂)
               (g : assembly_morphism X₂ X₃),
             comp_assembly_morphism_bi f g).
  Defined.

  Proposition precat_of_assembly_laws
    : is_precategory precat_data_of_assembly.
  Proof.
    use is_precategory_one_assoc_to_two.
    repeat split ; intros ; use assembly_morphism_eq ; intro ; apply idpath.
  Qed.
  
  Definition precat_of_assembly
    : precategory.
  Proof.
    use make_precategory.
    - exact precat_data_of_assembly.
    - exact precat_of_assembly_laws.
  Defined.

  Definition cat_of_assembly
    : category.
  Proof.
    use make_category.
    - exact precat_of_assembly.
    - abstract
        (intro ; intros ;
         apply isaset_assembly_morphism).
  Defined.
End CatOfAssemblies.
