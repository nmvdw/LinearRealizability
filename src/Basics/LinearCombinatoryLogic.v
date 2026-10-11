Require Import UniMath.MoreFoundations.All.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.

Declare Scope linear_combinatory_logic.
Delimit Scope linear_combinatory_logic with lcl.

Local Open Scope linear_combinatory_logic.
Local Open Scope logic.

(** * 1. Terms in linear combinatory logic *)
Inductive LCL (A : UU) : UU :=
| Base : A → LCL A
| Icomb : LCL A
| Bcomb : LCL A
| Ccomb : LCL A
| Kcomb : LCL A
| Wcomb : LCL A
| Dcomb : LCL A
| Delcomb : LCL A
| Fcomb : LCL A
| Excl : LCL A → LCL A
| App : LCL A → LCL A → LCL A.

Notation "'I'" := (Icomb _) : linear_combinatory_logic.
Notation "'B'" := (Bcomb _) : linear_combinatory_logic.
Notation "'C'" := (Ccomb _) : linear_combinatory_logic.
Notation "'K'" := (Kcomb _) : linear_combinatory_logic.
Notation "'W'" := (Wcomb _) : linear_combinatory_logic.
Notation "'D'" := (Dcomb _) : linear_combinatory_logic.
Notation "'δ'" := (Delcomb _) : linear_combinatory_logic.
Notation "'F'" := (Fcomb _) : linear_combinatory_logic.
Notation "'!' x" := (Excl _ x) : linear_combinatory_logic.
Notation "t · u" := (App _ t u) : linear_combinatory_logic.

(** * 2. Properties for relations on terms *)
Definition LCL_rel_I_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t : LCL A), R (I · t) t.

Definition LCL_rel_B_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t₁ t₂ t₃ : LCL A), R (B · t₁ · t₂ · t₃) (t₁ · (t₂ · t₃)).

Definition LCL_rel_C_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t₁ t₂ t₃ : LCL A), R (C · t₁ · t₂ · t₃) (t₁ · t₃ · t₂).

Definition LCL_rel_K_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t₁ t₂ : LCL A), R (K · t₁ · (! t₂)) t₁.

Definition LCL_rel_W_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t₁ t₂ : LCL A), R (W · t₁ · (! t₂)) (t₁ · (! t₂) · (! t₂)).

Definition LCL_rel_D_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t : LCL A), R (D · (! t)) t.

Definition LCL_rel_del_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t : LCL A), R (δ · (! t)) (!(! t)).

Definition LCL_rel_F_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t₁ t₂ : LCL A), R (F · (! t₁) · (! t₂)) (!(t₁ · t₂)).

Definition LCL_rel_excl_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t₁ t₂ : LCL A), R t₁ t₂ ⇒ R (! t₁) (! t₂).

Definition LCL_rel_app_eq
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t₁ t₂ u₁ u₂ : LCL A), R t₁ t₂ ⇒ R u₁ u₂ ⇒ R (t₁ · u₁) (t₂ · u₂).

Definition is_LCL_beta_rel
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : UU
  := LCL_rel_I_eq R
     × LCL_rel_B_eq R
     × LCL_rel_C_eq R
     × LCL_rel_K_eq R
     × LCL_rel_W_eq R
     × LCL_rel_D_eq R
     × LCL_rel_del_eq R
     × LCL_rel_F_eq R
     × LCL_rel_excl_eq R
     × LCL_rel_app_eq R.

Definition is_LCL_beta_rel_I_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_I_eq R
  := pr1 H.

Definition is_LCL_beta_rel_B_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_B_eq R
  := pr12 H.

Definition is_LCL_beta_rel_C_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_C_eq R
  := pr122 H.

Definition is_LCL_beta_rel_K_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_K_eq R
  := pr1 (pr222 H).

Definition is_LCL_beta_rel_W_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_W_eq R
  := pr12 (pr222 H).

Definition is_LCL_beta_rel_D_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_D_eq R
  := pr122 (pr222 H).

Definition is_LCL_beta_rel_del_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_del_eq R
  := pr1 (pr222 (pr222 H)).

Definition is_LCL_beta_rel_F_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_F_eq R
  := pr12 (pr222 (pr222 H)).

Definition is_LCL_beta_rel_excl_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_excl_eq R
  := pr122 (pr222 (pr222 H)).

Definition is_LCL_beta_rel_app_eq
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_beta_rel R)
  : LCL_rel_app_eq R
  := pr222 (pr222 (pr222 H)).

(** * 3. The least equivalence relation respecting β *)
Definition rel_least_LCL_beta_eqrel
           (A : UU)
  : LCL A → LCL A → hProp
  := λ t u, ∀ (R : LCL A → LCL A → hProp), is_LCL_beta_rel R ⇒ iseqrel R ⇒ R t u.

Definition is_eqrel_rel_least_LCL_beta_eqrel
           (A : UU)
  : iseqrel (rel_least_LCL_beta_eqrel A).
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

Definition eqrel_least_LCL_beta_eqrel
           (A : UU)
  : eqrel (LCL A)
  := make_eqrel (rel_least_LCL_beta_eqrel A) (is_eqrel_rel_least_LCL_beta_eqrel A).

(** * 4. Terms modulo β *)
Definition LCL_quot
           (A : UU)
  : hSet
  := setquotinset (eqrel_least_LCL_beta_eqrel A).

Definition LCL_quot_I
           (A : UU)
  : LCL_quot A
  := setquotpr _ I.

Definition LCL_quot_B
           (A : UU)
  : LCL_quot A
  := setquotpr _ B.

Definition LCL_quot_C
           (A : UU)
  : LCL_quot A
  := setquotpr _ C.

Definition LCL_quot_K
           (A : UU)
  : LCL_quot A
  := setquotpr _ K.

Definition LCL_quot_W
           (A : UU)
  : LCL_quot A
  := setquotpr _ W.

Definition LCL_quot_D
           (A : UU)
  : LCL_quot A
  := setquotpr _ D.

Definition LCL_quot_del
           (A : UU)
  : LCL_quot A
  := setquotpr _ δ.

Definition LCL_quot_F
           (A : UU)
  : LCL_quot A
  := setquotpr _ F.

Definition LCL_quot_app
           {A : UU}
  : LCL_quot A → LCL_quot A → LCL_quot A.
Proof.
  use setquotuniv2.
  - exact (λ t u, setquotpr _ (t · u)).
  - abstract
      (intros t₁ t₂ u₁ u₂ p q ;
       use iscompsetquotpr ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_app_eq HR₁ _ _ _ _ (p R HR₁ HR₂) (q R HR₁ HR₂))).
Defined.

Definition LCL_quot_excl
           {A : UU}
  : LCL_quot A → LCL_quot A.
Proof.
  use setquotuniv.
  - exact (λ t, setquotpr _ (! t)).
  - abstract
      (intros t₁ t₂ p ;
       use iscompsetquotpr ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_excl_eq HR₁ _ _ (p R HR₁ HR₂))).
Defined.

Definition LCL_applicative_structure
           (A : UU)
  : applicative_structure.
Proof.
  use make_applicative_structure.
  - exact (LCL_quot A).
  - exact LCL_quot_app.
Defined.

Definition LCL_linear_combinatory_algebra
           (A : UU)
  : linear_combinatory_algebra.
Proof.
  simple refine (make_linear_combinatory_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - exact (LCL_applicative_structure A).
  - exact LCL_quot_excl.
  - exact (LCL_quot_I A).
  - exact (LCL_quot_B A).
  - exact (LCL_quot_C A).
  - exact (LCL_quot_K A).
  - exact (LCL_quot_W A).
  - exact (LCL_quot_D A).
  - exact (LCL_quot_del A).
  - exact (LCL_quot_F A).
  - abstract
      (use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_I_eq HR₁ t)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; do 2 (use impred ; intro) ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₂ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₃ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_B_eq HR₁ t₁ t₂ t₃)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; do 2 (use impred ; intro) ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₂ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₃ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_C_eq HR₁ t₁ t₂ t₃)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₂ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_K_eq HR₁ t₁ t₂)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₂ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_W_eq HR₁ t₁ t₂)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_D_eq HR₁ t)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_del_eq HR₁ t)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₂ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_beta_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_F_eq HR₁ t₁ t₂)).
Defined.

(** * 5. Extensional relations *)
Definition LCL_rel_extensional
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : hProp
  := ∀ (t₁ t₂ : LCL A),
     (∀ (u : LCL A), R (t₁ · u) (t₂ · u)) ⇒ R t₁ t₂.

Definition is_LCL_ext_rel
           {A : UU}
           (R : LCL A → LCL A → hProp)
  : UU
  := is_LCL_beta_rel R
     × LCL_rel_extensional R.

Coercion is_LCL_ext_rel_to_beta_rel
         {A : UU}
         {R : LCL A → LCL A → hProp}
         (H : is_LCL_ext_rel R)
  : is_LCL_beta_rel R
  := pr1 H.

Definition is_LCL_ext_rel_extensional
           {A : UU}
           {R : LCL A → LCL A → hProp}
           (H : is_LCL_ext_rel R)
  : LCL_rel_extensional R
  := pr2 H.

Definition rel_least_LCL_ext_eqrel
           (A : UU)
  : LCL A → LCL A → hProp
  := λ t u, ∀ (R : LCL A → LCL A → hProp), is_LCL_ext_rel R ⇒ iseqrel R ⇒ R t u.

Definition is_eqrel_rel_least_LCL_ext_eqrel
           (A : UU)
  : iseqrel (rel_least_LCL_ext_eqrel A).
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

Definition eqrel_least_LCL_ext_eqrel
           (A : UU)
  : eqrel (LCL A)
  := make_eqrel (rel_least_LCL_ext_eqrel A) (is_eqrel_rel_least_LCL_ext_eqrel A).

(** * 6. Terms modulo β and η *)
Definition ext_LCL_quot
           (A : UU)
  : hSet
  := setquotinset (eqrel_least_LCL_ext_eqrel A).

Definition ext_LCL_quot_I
           (A : UU)
  : ext_LCL_quot A
  := setquotpr _ I.

Definition ext_LCL_quot_B
           (A : UU)
  : ext_LCL_quot A
  := setquotpr _ B.

Definition ext_LCL_quot_C
           (A : UU)
  : ext_LCL_quot A
  := setquotpr _ C.

Definition ext_LCL_quot_K
           (A : UU)
  : ext_LCL_quot A
  := setquotpr _ K.

Definition ext_LCL_quot_W
           (A : UU)
  : ext_LCL_quot A
  := setquotpr _ W.

Definition ext_LCL_quot_D
           (A : UU)
  : ext_LCL_quot A
  := setquotpr _ D.

Definition ext_LCL_quot_del
           (A : UU)
  : ext_LCL_quot A
  := setquotpr _ δ.

Definition ext_LCL_quot_F
           (A : UU)
  : ext_LCL_quot A
  := setquotpr _ F.

Definition ext_LCL_quot_app
           {A : UU}
  : ext_LCL_quot A → ext_LCL_quot A → ext_LCL_quot A.
Proof.
  use setquotuniv2.
  - exact (λ t u, setquotpr _ (t · u)).
  - abstract
      (intros t₁ t₂ u₁ u₂ p q ;
       use iscompsetquotpr ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_app_eq HR₁ _ _ _ _ (p R HR₁ HR₂) (q R HR₁ HR₂))).
Defined.

Definition ext_LCL_quot_excl
           {A : UU}
  : ext_LCL_quot A → ext_LCL_quot A.
Proof.
  use setquotuniv.
  - exact (λ t, setquotpr _ (! t)).
  - abstract
      (intros t₁ t₂ p ;
       use iscompsetquotpr ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_excl_eq HR₁ _ _ (p R HR₁ HR₂))).
Defined.
           
Definition ext_LCL_applicative_structure
           (A : UU)
  : applicative_structure.
Proof.
  use make_applicative_structure.
  - exact (ext_LCL_quot A).
  - exact ext_LCL_quot_app.
Defined.

Definition ext_LCL_combinatory_algebra
           (A : UU)
  : linear_combinatory_algebra.
Proof.
  simple refine (make_linear_combinatory_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - exact (ext_LCL_applicative_structure A).
  - exact ext_LCL_quot_excl.
  - exact (ext_LCL_quot_I A).
  - exact (ext_LCL_quot_B A).
  - exact (ext_LCL_quot_C A).
  - exact (ext_LCL_quot_K A).
  - exact (ext_LCL_quot_W A).
  - exact (ext_LCL_quot_D A).
  - exact (ext_LCL_quot_del A).
  - exact (ext_LCL_quot_F A).
  - abstract
      (use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_I_eq HR₁ t)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; do 2 (use impred ; intro) ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₂ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₃ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_B_eq HR₁ t₁ t₂ t₃)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; do 2 (use impred ; intro) ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₂ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₃ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_C_eq HR₁ t₁ t₂ t₃)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₂ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_K_eq HR₁ t₁ t₂)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₂ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_W_eq HR₁ t₁ t₂)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_D_eq HR₁ t)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_del_eq HR₁ t)).
  - abstract
      (use setquotunivprop' ;
       [ intro ; use impred ; intro ; apply setproperty | ] ;
       intros t₁ ;
       use setquotunivprop' ;
       [ intro ; apply setproperty | ] ;
       intros t₂ ;
       cbn ;
       use (iscompsetquotpr (eqrel_least_LCL_ext_eqrel A)) ;
       intros R HR₁ HR₂ ;
       exact (is_LCL_beta_rel_F_eq HR₁ t₁ t₂)).
Defined.

Proposition is_extensional_ext_LCL_combinatory_algebra
            (A : UU)
  : is_extensional_applicative_structure
      (ext_LCL_combinatory_algebra A).
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
  use (is_LCL_ext_rel_extensional HR₁).
  intros u.
  specialize (p (setquotpr _ u)).
  exact (setquotpreq _ _ _ p R HR₁ HR₂).
Qed.
