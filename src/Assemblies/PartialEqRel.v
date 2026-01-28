(**

 Partial equivalence relations

 Contents
 1. Partial equivalence relations for a combinatory algebra
 2. The domain of a PER
 3. Morphisms between PERs
 4. The identity and composition of PER morphisms
 5. The category of PERs

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.

Local Open Scope bi.

(** * 1. Partial equivalence relations for a combinatory algebra *)
Definition ca_per
           (A : bi_algebra)
  : UU
  := ∑ (R : hrel A), issymm R × istrans R.

Proposition isaset_ca_per
            (A : bi_algebra)
  : isaset (ca_per A).
Proof.
  use isaset_total2.
  - apply isaset_hrel.
  - intro R.
    use isasetaprop.
    use isapropdirprod.
    + apply isaprop_issymm.
    + apply isaprop_istrans.
Qed.

Definition ca_per_hSet
           (A : bi_algebra)
  : hSet
  := make_hSet (ca_per A) (isaset_ca_per A).
           
Definition make_ca_per
           {A : bi_algebra}
           (R : hrel A)
           (H₁ : issymm R)
           (H₂ : istrans R)
  : ca_per A
  := R ,, H₁ ,, H₂.
           
Coercion hrel_of_ca_per
         {A : bi_algebra}
         (R : ca_per A)
  : hrel A
  := pr1 R.

Proposition issymm_ca_per
            {A : bi_algebra}
            (R : ca_per A)
            {a₁ a₂ : A}
            (p : R a₁ a₂)
  : R a₂ a₁.
Proof.
  exact (pr12 R _ _ p).
Defined.

Proposition istrans_ca_per
            {A : bi_algebra}
            (R : ca_per A)
            {a₁ a₂ a₃ : A}
            (p : R a₁ a₂)
            (q : R a₂ a₃)
  : R a₁ a₃.
Proof.
  exact (pr22 R _ _ _ p q).
Defined.

Proposition refl_l_ca_per
            {A : bi_algebra}
            {R : ca_per A}
            {a₁ a₂ : A}
            (p : R a₁ a₂)
  : R a₁ a₁.
Proof.
  refine (istrans_ca_per R p _).
  use issymm_ca_per.
  exact p.
Qed.

Proposition refl_r_ca_per
            {A : bi_algebra}
            {R : ca_per A}
            {a₁ a₂ : A}
            (p : R a₁ a₂)
  : R a₂ a₂.
Proof.
  refine (refl_l_ca_per _).
  use issymm_ca_per.
  exact p.
Qed.

Proposition ca_per_weq_left
            {A : bi_algebra}
            {R : ca_per A}
            (a : A)
            {x₁ x₂ : A}
            (p : R x₁ x₂)
  : R a x₁ = R a x₂.
Proof.
  use weqtopathshProp.
  use weqimplimpl.
  - intro q.
    exact (istrans_ca_per _ q p).
  - intro q.
    exact (istrans_ca_per _ q (issymm_ca_per _ p)).
  - apply propproperty. 
  - apply propproperty. 
Qed.

Proposition ca_per_weq_right
            {A : bi_algebra}
            {R : ca_per A}
            (a : A)
            {x₁ x₂ : A}
            (p : R x₁ x₂)
  : R x₁ a = R x₂ a.
Proof.
  use weqtopathshProp.
  use weqimplimpl.
  - intro q.
    exact (istrans_ca_per _ (issymm_ca_per _ p) q).
  - intro q.
    exact (istrans_ca_per _ p q).
  - apply propproperty. 
  - apply propproperty. 
Qed.

(** * 2. The domain of a PER *)
Definition dom_ca_per
           {A : bi_algebra}
           (R : ca_per A)
  : UU
  := ∑ (a : A), R a a.

Definition make_dom_ca_per
           {A : bi_algebra}
           {R : ca_per A}
           (a : A)
           (p : R a a)
  : dom_ca_per R
  := a ,, p.

Coercion dom_ca_per_el
         {A : bi_algebra}
         {R : ca_per A}
         (a : dom_ca_per R)
  : A
  := pr1 a.

Proposition dom_ca_per_refl
            {A : bi_algebra}
            {R : ca_per A}
            (a : dom_ca_per R)
  : R a a.
Proof.
  exact (pr2 a).
Defined.

Proposition dom_ca_per_quot_iseqrel
            {A : bi_algebra}
            (R : ca_per A)
  : iseqrel (λ (x₁ x₂ : dom_ca_per R), R x₁ x₂).
Proof.
  repeat split.
  - intros x₁ x₂ x₃.
    exact (istrans_ca_per R).
  - intro x.
    apply dom_ca_per_refl.
  - intros x₁ x₂.
    exact (issymm_ca_per R).
Qed.
    
Definition dom_ca_per_quot_eqrel
           {A : bi_algebra}
           (R : ca_per A)
  : eqrel (dom_ca_per R).
Proof.
  use make_eqrel.
  - exact (λ (x₁ x₂ : dom_ca_per R), R x₁ x₂).
  - exact (dom_ca_per_quot_iseqrel R).
Defined.
    
Definition dom_ca_per_quot
           {A : bi_algebra}
           (R : ca_per A)
  : hSet.
Proof.
  use setquotinset.
  - exact (dom_ca_per R).
  - exact (dom_ca_per_quot_eqrel R).
Defined.

(** * 3. Morphisms between PERs *)
Definition ca_per_tracker
           {A : bi_algebra}
           (R₁ R₂ : ca_per A)
  : UU
  := ∑ (b : A), ∏ (a₁ a₂ : A), R₁ a₁ a₂ → R₂ (b · a₁) (b · a₂).

Definition make_ca_per_tracker
           {A : bi_algebra}
           {R₁ R₂ : ca_per A}
           (b : A)
           (Hb : ∏ (a₁ a₂ : A), R₁ a₁ a₂ → R₂ (b · a₁) (b · a₂))
  : ca_per_tracker R₁ R₂
  := b ,, Hb.

Coercion tracker_to_el
         {A : bi_algebra}
         {R₁ R₂ : ca_per A}
         (b : ca_per_tracker R₁ R₂)
  : A
  := pr1 b.

Proposition ca_per_tracker_map_related
            {A : bi_algebra}
            {R₁ R₂ : ca_per A}
            (b : ca_per_tracker R₁ R₂)
            {a₁ a₂ : A}
            (p : R₁ a₁ a₂)
  : R₂ (b · a₁) (b · a₂).
Proof.
  exact (pr2 b a₁ a₂ p).
Defined.
            
Definition ca_per_tracker_eqrel
           {A : bi_algebra}
           (R₁ R₂ : ca_per A)
  : eqrel (ca_per_tracker R₁ R₂).
Proof.
  use make_eqrel.
  - exact (λ b₁ b₂, ∀ (a : A), R₁ a a ⇒ R₂ (b₁ · a) (b₂ · a))%logic.
  - repeat split.
    + abstract
        (intros b₁ b₂ b₃ p q r a ;
         exact (istrans_ca_per _ (p r a) (q r a))).
    + abstract
        (intros b r a ;
         use ca_per_tracker_map_related ;
         exact a).
    + abstract
        (intros b₁ b₂ p r a ;
         exact (issymm_ca_per _ (p r a))).
Defined.

Definition ca_per_morphism
           {A : bi_algebra}
           (R₁ R₂ : ca_per A)
  : hSet
  := setquotinset (ca_per_tracker_eqrel R₁ R₂).

Definition ca_per_morphism_function
           {A : bi_algebra}
           {R₁ R₂ : ca_per A}
  : ca_per_morphism R₁ R₂ → dom_ca_per_quot R₁ → dom_ca_per_quot R₂.
Proof.
  use setquotuniv2'.
  - refine (λ a b, setquotpr _ _).
    use make_dom_ca_per.
    + exact (a · b).
    + abstract
        (apply (ca_per_tracker_map_related a) ;
         apply dom_ca_per_refl).
  - split.
    + abstract
        (intros a₁ a₂ p b ;
         use iscompsetquotpr ; cbn ;
         refine (p b _) ;
         apply dom_ca_per_refl).
    + abstract
        (intros b₁ b₂ q a ;
         use iscompsetquotpr ; cbn ;
         apply ca_per_tracker_map_related ;
         apply q).
Defined.

(** * 4. The identity and composition of PER morphisms *)
Definition id_ca_per_morphism
           {A : bi_algebra}
           (R : ca_per A)
  : ca_per_morphism R R.
Proof.
  use setquotpr.
  refine (I ,, _).
  abstract
    (intros a₁ a₂ p ;
     rewrite !bi_algebra_i_eq ;
     exact p).
Defined.

Definition comp_ca_per_morphism
           {A : bi_algebra}
           {R₁ R₂ R₃ : ca_per A}
           (φ : ca_per_morphism R₁ R₂)
           (ψ : ca_per_morphism R₂ R₃)
  : ca_per_morphism R₁ R₃.
Proof.
  revert φ ψ.
  use setquotuniv2'.
  - intros a₁ a₂.
    use setquotpr.
    use make_ca_per_tracker.
    + exact (B · a₂ · a₁).
    + abstract
        (intros b₁ b₂ p ;
         rewrite !bi_algebra_b_eq ;
         apply (ca_per_tracker_map_related a₂) ;
         apply (ca_per_tracker_map_related a₁) ;
         exact p).
  - split.
    + abstract
        (intros a₁ a₂ p b ;
         use iscompsetquotpr ;
         intros c q ; cbn ;
         rewrite !bi_algebra_b_eq ;
         apply (ca_per_tracker_map_related b) ;
         exact (p c q)).
    + abstract
        (intros b₁ b₂ p a ;
         use iscompsetquotpr ;
         intros c q ; cbn ;
         rewrite !bi_algebra_b_eq ;
         refine (p (a · c) _) ;
         apply (ca_per_tracker_map_related a) ;
         exact q).
Defined.

(** * 5. The category of PERs *)
Definition precat_of_ca_pers_ob_mor
           (A : bi_algebra)
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (ca_per A).
  - exact ca_per_morphism.
Defined.

Definition precat_of_ca_pers_data
           (A : bi_algebra)
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact (precat_of_ca_pers_ob_mor A).
  - exact id_ca_per_morphism.
  - exact (λ _ _ _ f g, comp_ca_per_morphism f g).
Defined.

Proposition precat_of_ca_pers_laws
            (A : bi_algebra)
  : is_precategory (precat_of_ca_pers_data A).
Proof.
  use is_precategory_one_assoc_to_two.
  repeat split.
  - intros R₁ R₂.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intro a.
    use iscompsetquotpr ; cbn.
    intros b p.
    rewrite bi_algebra_b_eq.
    rewrite bi_algebra_i_eq.
    apply (ca_per_tracker_map_related a).
    exact p.
  - intros R₁ R₂.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intro a.
    use iscompsetquotpr ; cbn.
    intros b p.
    rewrite bi_algebra_b_eq.
    rewrite bi_algebra_i_eq.
    apply (ca_per_tracker_map_related a).
    exact p.
  - intros R₁ R₂ R₃ R₄.
    use setquotunivprop'.
    {
      intro.
      repeat (use impred ; intro).
      apply setproperty.
    }
    intro a₁.
    use setquotunivprop'.
    {
      intro.
      repeat (use impred ; intro).
      apply setproperty.
    }
    intro a₂.
    use setquotunivprop'.
    {
      intro.
      apply setproperty.
    }
    intro a₃.
    use iscompsetquotpr ; cbn.
    intros b p.
    rewrite !bi_algebra_b_eq.
    apply (ca_per_tracker_map_related a₃).
    apply (ca_per_tracker_map_related a₂).
    apply (ca_per_tracker_map_related a₁).
    exact p.
Qed.

Definition precat_of_ca_pers
           (A : bi_algebra)
  : precategory.
Proof.
  use make_precategory.
  - exact (precat_of_ca_pers_data A).
  - exact (precat_of_ca_pers_laws A).
Defined.

Definition cat_of_ca_pers
           (A : bi_algebra)
  : category.
Proof.
  use make_category.
  - exact (precat_of_ca_pers A).
  - abstract
      (intros ? ? ;
       apply setproperty).
Defined.
