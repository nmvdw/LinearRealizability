Require Import UniMath.MoreFoundations.All.

Require Import Basics.CombinatoryAlgebra.

Declare Scope combinatory_logic.
Delimit Scope combinatory_logic with cl.

Local Open Scope combinatory_logic.
Local Open Scope logic.

(** * 1. Terms in combinatory logic *)
Inductive CL (A : UU) : UU :=
| Base : A → CL A
| Kcomb : CL A
| Scomb : CL A
| App : CL A → CL A → CL A.

Notation "'K'" := (Kcomb _) : combinatory_logic.
Notation "'S'" := (Scomb _) : combinatory_logic.
Notation "t · u" := (App _ t u) : combinatory_logic.

(** * 2. Properties for relations on terms *)
Definition CL_rel_K_eq
           {A : UU}
           (R : CL A → CL A → hProp)
  : hProp
  := ∀ (t₁ t₂ : CL A), R (K · t₁ · t₂) t₁.

Definition CL_rel_S_eq
           {A : UU}
           (R : CL A → CL A → hProp)
  : hProp
  := ∀ (t₁ t₂ t₃ : CL A), R (S · t₁ · t₂ · t₃) (t₁ · t₃ · (t₂ · t₃)).

Definition CL_rel_app_eq
           {A : UU}
           (R : CL A → CL A → hProp)
  : hProp
  := ∀ (t₁ t₂ u₁ u₂ : CL A), R t₁ t₂ ⇒ R u₁ u₂ ⇒ R (t₁ · u₁) (t₂ · u₂).

Definition is_CL_beta_rel
           {A : UU}
           (R : CL A → CL A → hProp)
  : UU
  := CL_rel_K_eq R × CL_rel_S_eq R × CL_rel_app_eq R.

Definition is_CL_beta_rel_K_eq
           {A : UU}
           {R : CL A → CL A → hProp}
           (H : is_CL_beta_rel R)
  : CL_rel_K_eq R
  := pr1 H.

Definition is_CL_beta_rel_S_eq
           {A : UU}
           {R : CL A → CL A → hProp}
           (H : is_CL_beta_rel R)
  : CL_rel_S_eq R
  := pr12 H.

Definition is_CL_beta_rel_app_eq
           {A : UU}
           {R : CL A → CL A → hProp}
           (H : is_CL_beta_rel R)
  : CL_rel_app_eq R
  := pr22 H.

(** * 3. The least equivalence relation respecting β *)
Definition rel_least_CL_beta_eqrel
           (A : UU)
  : CL A → CL A → hProp
  := λ t u, ∀ (R : CL A → CL A → hProp), is_CL_beta_rel R ⇒ iseqrel R ⇒ R t u.

Definition is_eqrel_rel_least_CL_beta_eqrel
           (A : UU)
  : iseqrel (rel_least_CL_beta_eqrel A).
Proof.
  repeat split.
  - intros t₁ t₂ t₃ p q R HR₁ HR₂.
    use (pr11 HR₂).
    + exact t₂.
    + exact (p R HR₁ HR₂).
    + exact (q R HR₁ HR₂).
  - intros t R HR₁ HR₂.
    apply HR₂.
  - intros t u p R HR₁ HR₂.
    apply HR₂.
    exact (p R HR₁ HR₂).
Qed.

Definition eqrel_least_CL_beta_eqrel
           (A : UU)
  : eqrel (CL A)
  := make_eqrel (rel_least_CL_beta_eqrel A) (is_eqrel_rel_least_CL_beta_eqrel A).

(** * 4. Terms modulo β *)
Definition CL_quot
           (A : UU)
  : hSet
  := setquotinset (eqrel_least_CL_beta_eqrel A).

Definition CL_quot_K
           (A : UU)
  : CL_quot A
  := setquotpr _ K.

Definition CL_quot_S
           (A : UU)
  : CL_quot A
  := setquotpr _ S.

Definition CL_quot_app
           {A : UU}
  : CL_quot A → CL_quot A → CL_quot A.
Proof.
  use setquotuniv2.
  - exact (λ t u, setquotpr _ (t · u)).
  - abstract
      (intros t₁ t₂ u₁ u₂ p q ;
       use iscompsetquotpr ;
       intros R HR₁ HR₂ ;
       exact (is_CL_beta_rel_app_eq HR₁ _ _ _ _ (p R HR₁ HR₂) (q R HR₁ HR₂))).
Defined.
           
Definition CL_applicative_structure
           (A : UU)
  : applicative_structure.
Proof.
  use make_applicative_structure.
  - exact (CL_quot A).
  - exact CL_quot_app.
Defined.

Definition CL_combinatory_algebra
           (A : UU)
  : combinatory_algebra.
Proof.
  use make_combinatory_algebra.
  - exact (CL_applicative_structure A).
  - exact (CL_quot_K A).
  - exact (CL_quot_S A).
  - abstract
      (use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intro t ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intro u ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_CL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_CL_beta_rel_K_eq HR₁ t u)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; repeat (use impred ; intro) ; apply setproperty | ] ;
       intro t₁ ;
       use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intro t₂ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intro t₃ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_CL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_CL_beta_rel_S_eq HR₁ t₁ t₂ t₃)).
Defined.

(** * 5. Extensional relations *)
Definition CL_rel_extensional
           {A : UU}
           (R : CL A → CL A → hProp)
  : hProp
  := ∀ (t₁ t₂ : CL A),
     (∀ (u : CL A), R (t₁ · u) (t₂ · u)) ⇒ R t₁ t₂.

Definition is_CL_ext_rel
           {A : UU}
           (R : CL A → CL A → hProp)
  : UU
  := is_CL_beta_rel R
     × CL_rel_extensional R.

Coercion is_CL_ext_rel_to_beta_rel
         {A : UU}
         {R : CL A → CL A → hProp}
         (H : is_CL_ext_rel R)
  : is_CL_beta_rel R
  := pr1 H.

Definition is_CL_ext_rel_extensional
           {A : UU}
           {R : CL A → CL A → hProp}
           (H : is_CL_ext_rel R)
  : CL_rel_extensional R
  := pr2 H.

Definition rel_least_CL_ext_eqrel
           (A : UU)
  : CL A → CL A → hProp
  := λ t u, ∀ (R : CL A → CL A → hProp), is_CL_ext_rel R ⇒ iseqrel R ⇒ R t u.

Definition is_eqrel_rel_least_CL_ext_eqrel
           (A : UU)
  : iseqrel (rel_least_CL_ext_eqrel A).
Proof.
  repeat split.
  - intros t₁ t₂ t₃ p q R HR₁ HR₂.
    use (pr11 HR₂).
    + exact t₂.
    + exact (p R HR₁ HR₂).
    + exact (q R HR₁ HR₂).
  - intros t R HR₁ HR₂.
    apply HR₂.
  - intros t u p R HR₁ HR₂.
    apply HR₂.
    exact (p R HR₁ HR₂).
Qed.

Definition eqrel_least_CL_ext_eqrel
           (A : UU)
  : eqrel (CL A)
  := make_eqrel (rel_least_CL_ext_eqrel A) (is_eqrel_rel_least_CL_ext_eqrel A).

(** * 6. Terms modulo β and η *)
Definition ext_CL_quot
           (A : UU)
  : hSet
  := setquotinset (eqrel_least_CL_ext_eqrel A).

Definition ext_CL_quot_K
           (A : UU)
  : ext_CL_quot A
  := setquotpr _ K.

Definition ext_CL_quot_S
           (A : UU)
  : ext_CL_quot A
  := setquotpr _ S.

Definition ext_CL_quot_app
           {A : UU}
  : ext_CL_quot A → ext_CL_quot A → ext_CL_quot A.
Proof.
  use setquotuniv2.
  - exact (λ t u, setquotpr _ (t · u)).
  - abstract
      (intros t₁ t₂ u₁ u₂ p q ;
       use iscompsetquotpr ;
       intros R HR₁ HR₂ ;
       exact (is_CL_beta_rel_app_eq HR₁ _ _ _ _ (p R HR₁ HR₂) (q R HR₁ HR₂))).
Defined.
           
Definition ext_CL_applicative_structure
           (A : UU)
  : applicative_structure.
Proof.
  use make_applicative_structure.
  - exact (ext_CL_quot A).
  - exact ext_CL_quot_app.
Defined.

Definition ext_CL_combinatory_algebra
           (A : UU)
  : combinatory_algebra.
Proof.
  use make_combinatory_algebra.
  - exact (ext_CL_applicative_structure A).
  - exact (ext_CL_quot_K A).
  - exact (ext_CL_quot_S A).
  - abstract
      (use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intro t ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intro u ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_CL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_CL_beta_rel_K_eq HR₁ t u)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; repeat (use impred ; intro) ; apply setproperty | ] ;
       intro t₁ ;
       use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intro t₂ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intro t₃ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_CL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_CL_beta_rel_S_eq HR₁ t₁ t₂ t₃)).
Defined.

Proposition is_extensional_ext_CL_combinatory_algebra
            (A : UU)
  : is_extensional_applicative_structure
      (ext_CL_combinatory_algebra A).
Proof.
  use setquotunivprop'.
  {
    intro.
    repeat (use impred ; intro).
    apply setproperty.
  }
  intro t₁.
  use setquotunivprop'.
  {
    intro.
    use impred ; intro.
    apply setproperty.
  }
  intros t₂ p.
  use iscompsetquotpr.
  intros R HR₁ HR₂.
  use (is_CL_ext_rel_extensional HR₁).
  intros u.
  specialize (p (setquotpr _ u)).
  exact (setquotpreq _ _ _ p R HR₁ HR₂).
Qed.
