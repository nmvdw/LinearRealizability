(**

 The realizability tripos

 Contents
 1. The displayed category of realizability predicates
 2. Cleaving for realizability predicates
 3. The realizability hyperdoctrine (without connectives)
 4. Connectives
 5. The realizability first-order hyperdoctrine
 6. The realizability tripos

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.

Local Open Scope ca.
Local Open Scope cat.

Section RealizabilityTripos.
  Context {A : combinatory_algebra}.

  (** * 1. The displayed category of realizability predicates *)
  Definition realizability_disp_cat_ob_mor
    : disp_cat_ob_mor SET.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (X : hSet), X → A → hProp).
    - exact (λ (X₁ X₂ : hSet)
               (Φ₁ : X₁ → A → hProp)
               (Φ₂ : X₂ → A → hProp)
               (f : X₁ → X₂),
             ∃ (a : A), ∀ (x : X₁) (b : A), Φ₁ x b ⇒ Φ₂ (f x) (a · b)%ca)%logic.
  Defined.

  Proposition realizability_disp_cat_id_comp
    : disp_cat_id_comp SET realizability_disp_cat_ob_mor.
  Proof.
    split.
    - intros X Φ.
      use hinhpr.
      refine (I ,, _).
      intros x b p ; cbn.
      rewrite combinatory_algebra_i_eq.
      exact p.
    - intros X₁ X₂ X₃ f g Φ₁ Φ₂ Φ₃ p.
      use factor_through_squash_hProp.
      intros ( a₂ & q₂ ).
      revert p.
      use factor_through_squash_hProp.
      intros ( a₁ & q₁ ).
      use hinhpr.
      refine (B · a₂ · a₁ ,, _)%ca.
      intros x b r ; cbn.
      rewrite combinatory_algebra_b_eq.
      use q₂.
      use q₁.
      exact r.
  Qed.
  
  Definition realizability_disp_cat_data
      : disp_cat_data SET.
  Proof.
    simple refine (_ ,, _).
    - exact realizability_disp_cat_ob_mor.
    - exact realizability_disp_cat_id_comp.
  Defined.

  Proposition locally_propositional_realizability_disp_cat
    : locally_propositional realizability_disp_cat_data.
  Proof.
    intros X Y f Φ₁ Φ₂.
    apply propproperty.
  Qed.

  Proposition realizability_disp_cat_axioms
    : disp_cat_axioms SET realizability_disp_cat_data.
  Proof.
    repeat split ; intros.
    - apply locally_propositional_realizability_disp_cat.
    - apply locally_propositional_realizability_disp_cat.
    - apply locally_propositional_realizability_disp_cat.
    - apply isasetaprop.
      apply locally_propositional_realizability_disp_cat.
  Qed.
  
  Definition realizability_disp_cat
    : disp_cat SET.
  Proof.
    simple refine (_ ,, _).
    - exact realizability_disp_cat_data.
    - exact realizability_disp_cat_axioms.
  Defined.

  (** * 2. Cleaving for realizability predicates *)
  Definition cleaving_realizability_disp_cat
    : cleaving realizability_disp_cat.
  Proof.
    refine (λ (X₁ X₂ : hSet) (f : X₂ → X₁) (Φ : X₁ → A → hProp), _).
    simple refine (_ ,, _ ,, _).
    - exact (λ (x : X₂) (a : A), Φ (f x) a).
    - abstract
        (use hinhpr ;
         refine (I ,, _) ;
         intros x b p ;
         rewrite combinatory_algebra_i_eq ;
         exact p).
    - refine (λ (X₀ : hSet) (g : X₀ → X₂) (Φ' : X₀ → A → hProp) hh, _).
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros gg₁ gg₂ ;
           use subtypePath ; [ intro ; apply homsets_disp | ] ;
           apply locally_propositional_realizability_disp_cat).
      + abstract
          (simple refine (_ ,, _) ;
           [ | apply locally_propositional_realizability_disp_cat ] ;
           revert hh ;
           use factor_through_squash_hProp ;
           intros ( a & p ) ;
           use hinhpr ;
           refine (a ,, _) ;
           intros x b q ;
           exact (p x b q)).
  Defined.

  (** * 3. The realizability hyperdoctrine (without connectives) *)
  Definition realizability_preorder_hyperdoctrine
    : preorder_hyperdoctrine.
  Proof.
    use make_preorder_hyperdoctrine.
    - exact SET.
    - exact realizability_disp_cat.
    - exact TerminalHSET.
    - exact BinProductsHSET.
    - exact cleaving_realizability_disp_cat.
    - exact locally_propositional_realizability_disp_cat.
  Defined.

  (** * 4. Connectives *)
  Definition fiberwise_terminal_realizability
    : fiberwise_terminal cleaving_realizability_disp_cat.
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - exact locally_propositional_realizability_disp_cat.
    - exact (λ (X : hSet) (x : X) (a : A), htrue).
    - abstract
        (intros X Φ ;
         use hinhpr ;
         refine (I ,, _) ;
         intros x b p ; cbn ;
         exact tt).
    - abstract
        (intros X₁ X₂ s ;
         use hinhpr ;
         refine (I ,, _) ;
         intros x b p ; cbn ;
         exact tt).
  Defined.

  Definition fiberwise_initial_realizability
    : fiberwise_initial cleaving_realizability_disp_cat.
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - exact locally_propositional_realizability_disp_cat.
    - exact (λ (X : hSet) (x : X) (a : A), hfalse).
    - abstract
        (intros X Φ ;
         use hinhpr ;
         refine (I ,, _) ;
         intros x y p ;
         induction p).
    - abstract
        (intros X₁ X₂ s ;
         use hinhpr ;
         refine (I ,, _) ;
         intros x b p ;
         induction p).
  Defined.

  Definition fiberwise_binproducts_realizability
    : fiberwise_binproducts cleaving_realizability_disp_cat.
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - exact locally_propositional_realizability_disp_cat.
    - exact (λ (X : hSet) (Φ₁ Φ₂ : X → A → hProp) (x : X) (a : A),
             hconj (Φ₁ x (π₁ · a)) (Φ₂ x (π₂ · a)))%ca.
    - abstract
        (intros X Φ₁ Φ₂ ;
         use hinhpr ;
         refine (π₁ ,, _) ;
         intros x b p ;
         exact (pr1 p)).
    - abstract
        (intros X Φ₁ Φ₂ ;
         use hinhpr ;
         refine (π₂ ,, _) ;
         intros x b p ;
         exact (pr2 p)).
    - abstract
        (intros X Φ₁ Φ₂ Φ₃ p ;
         use factor_through_squash_hProp ;
         intros ( a₂ & p₂ ) ;
         revert p ;
         use factor_through_squash_hProp ;
         intros ( a₁ & p₁ ) ;
         use hinhpr ;
         refine (pairf · a₁ · a₂ ,, _)%ca ;
         intros x b p ;
         rewrite combinatory_algebra_pr1_pair_fun ;
         rewrite combinatory_algebra_pr2_pair_fun ;
         specialize (p₁ x b p) ;
         specialize (p₂ x b p) ;
         cbn in p₁, p₂ ;
         exact (p₁ ,, p₂)).
    - abstract
        (intros X₁ X₂ s Φ₁ Φ₂ ;
         use hinhpr ;
         refine (I ,, _) ;
         intros x y ( p & q ) ;
         simpl in p, q ; simpl ;
         rewrite !combinatory_algebra_i_eq ;
         exact (p ,, q)).
  Defined.

  Definition fiberwise_bincoproducts_realizability
    : fiberwise_bincoproducts cleaving_realizability_disp_cat.
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - exact locally_propositional_realizability_disp_cat.
    - exact (λ (X : hSet) (Φ₁ Φ₂ : X → A → hProp) (x : X) (a : A),
             hdisj
               (hconj (K = π₁ · a)%logic (Φ₁ x (π₂ · a)))
               (hconj (K* = π₁ · a)%logic (Φ₂ x (π₂ · a))))%ca.
    - abstract
        (intros X Φ₁ Φ₂ ;
         use hinhpr ;
         refine (pair · K ,, _)%ca ;
         intros x a p ;
         use hinhpr ;
         use inl ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         refine (idpath _ ,, _) ;
         exact p).
    - abstract
        (intros X Φ₁ Φ₂ ;
         use hinhpr ;
         refine (pair · K* ,, _)%ca ;
         intros x a p ;
         use hinhpr ;
         use inr ;
         rewrite combinatory_algebra_pr1_pair ;
         rewrite combinatory_algebra_pr2_pair ;
         refine (idpath _ ,, _) ;
         exact p).
    - abstract
        (intros X Φ₁ Φ₂ Φ₃ ;
         intro p ;
         use factor_through_squash_hProp ;
         intros ( a₂ & p₂ ) ;
         revert p ;
         use factor_through_squash_hProp ;
         intros ( a₁ & p₁ ) ;
         use hinhpr ;
         refine (sumf · a₁ · a₂ ,, _)%ca ;
         intros x b ;
         use factor_through_squash_hProp ;
         intros [ [ q₁ q₂ ] | [ q₁ q₂ ]] ;
         [ rewrite (combinatory_algebra_sum_fun_inl _ _ _ (!q₁)) ;
           use p₁ ;
           exact q₂
         | rewrite (combinatory_algebra_sum_fun_inr _ _ _ (!q₁)) ;
           use p₂ ;
           exact q₂ ]).
    - abstract
        (intros X₁ X₂ f Φ₁ Φ₂ ;
         use hinhpr ;
         refine (I ,, _) ;
         intros x b ;
         rewrite !combinatory_algebra_i_eq ;
         intro p ;
         exact p).
  Defined.

  Definition fiberwise_exponentials_realizability
    : fiberwise_exponentials fiberwise_binproducts_realizability.
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - exact locally_propositional_realizability_disp_cat.
    - exact (λ (X : hSet) (Φ₁ Φ₂ : X → A → hProp) (x : X) (a : A),
             ∀ (b : A), himpl (Φ₁ x b) (Φ₂ x (a · b)%ca)).
    - abstract
        (intros X Φ₁ Φ₂ ;
         use hinhpr ;
         refine (ε ,, _) ;
         intros x a ( p₁ & p₂ ) ; simpl ;
         rewrite combinatory_algebra_eval_eq ;
         exact (p₂ _ p₁)).
    - abstract
        (intros X φ₁ Φ₂ Φ₃ ;
         use factor_through_squash_hProp ;
         intros ( a & p ) ;
         use hinhpr ;
         refine (lam · a ,, _)%ca ;
         intros x b₁ q₁ b₂ q₂ ;
         simpl in p ;
         specialize (p x (pair · b₂ · b₁)%ca) ;
         rewrite combinatory_algebra_pr1_pair in p ;
         rewrite combinatory_algebra_pr2_pair in p ;
         specialize (p (q₂ ,, q₁)) ;
         rewrite combinatory_algebra_lam_eq ;
         exact p).
    - abstract
        (intros X₁ X₂ s Φ₁ Φ₂ ;
         use hinhpr ;
         refine (I ,, _) ; simpl ;
         intros x a p b q ;
         rewrite combinatory_algebra_i_eq ;
         use p ;
         exact q).
  Defined.

  Definition has_dependent_products_realizability
    : has_dependent_products cleaving_realizability_disp_cat.
  Proof.
    use make_has_dependent_products_poset.
    - exact locally_propositional_realizability_disp_cat.
    - exact (λ (X₁ X₂ : hSet)
               (s : X₁ → X₂)
               (Φ : X₁ → A → hProp)
               (y : X₂)
               (a : A),
             ∀ (x : X₁), s x = y ⇒ Φ x a)%logic.
    - abstract
        (intros X₁ X₂ s Φ ;
         use hinhpr ;
         refine (I ,, _) ; simpl ;
         intros x a p ;
         rewrite combinatory_algebra_i_eq ;
         use p ;
         apply idpath).
    - abstract
        (intros X₁ X₂ s Φ₁ Φ₂ ;
         use factor_through_squash_hProp ;
         intros ( a & p ) ;
         simpl in p ;
         use hinhpr ;
         refine (a ,, _) ;
         intros y b q x r ;
         cbn in r ;
         induction r ;
         exact (p _ _ q)).
    - abstract
        (intros X₁ X₂ X₃ X₄ f₁ f₂ f₃ f₄ p Hp Φ ;
         use hinhpr ;
         refine (I ,, _) ;
         simpl in * ;
         intros x a q y r ;
         rewrite combinatory_algebra_i_eq ;
         specialize (q (el_pullback_set Hp y x r) (el_pullback_set_pr2 Hp y x r)) ;
         rewrite el_pullback_set_pr1 in q ;
         exact q).
  Defined.

  Definition has_dependent_sums_realizability
    : has_dependent_sums cleaving_realizability_disp_cat.
  Proof.
    use make_has_dependent_sums_poset.
    - exact locally_propositional_realizability_disp_cat.
    - exact (λ (X₁ X₂ : hSet)
               (s : X₁ → X₂)
               (Φ : X₁ → A → hProp)
               (y : X₂)
               (a : A),
             ∃ (x : X₁), hconj (s x = y)%logic (Φ x a)).
    - abstract
        (intros X₁ X₂ s Φ ;
         use hinhpr ;
         refine (I ,, _) ;
         intros x a p ;
         use hinhpr ;
         refine (x ,, idpath _ ,, _) ;
         rewrite combinatory_algebra_i_eq ;
         exact p).
    - abstract
        (intros X₁ X₂ s Φ Ψ ;
         use factor_through_squash_hProp ;
         intros ( a & p ) ;
         use hinhpr ;
         refine (a ,, _) ;
         intros y b ;
         use factor_through_squash_hProp ;
         intros ( x & q₁ & q₂ ) ;
         cbn in q₁ ; induction q₁ ;
         cbn ;
         use p ;
         exact q₂).
    - abstract
        (intros X₁ X₂ X₃ X₄ f₁ f₂ f₃ f₄ p Hp Φ ;
         use hinhpr ;
         refine (I ,, _) ;
         intros x a ;
         use factor_through_squash_hProp ;
         intros ( y & q₁ & q₂ ) ;
         use hinhpr ;
         refine (el_pullback_set Hp y x q₁ ,, _) ;
         refine (el_pullback_set_pr2 Hp y x q₁ ,, _) ;
         simpl ;
         rewrite combinatory_algebra_i_eq ;
         rewrite el_pullback_set_pr1 ;
         exact q₂).
  Defined.
  
  (** * 5. The realizability first-order hyperdoctrine *)
  Definition realizability_first_order_preoder_hyperdoctrine
    : first_order_preorder_hyperdoctrine.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _) ; cbn.
    - exact realizability_preorder_hyperdoctrine.
    - exact fiberwise_terminal_realizability.
    - exact fiberwise_initial_realizability.
    - exact fiberwise_binproducts_realizability.
    - exact fiberwise_bincoproducts_realizability.
    - exact fiberwise_exponentials_realizability.
    - exact has_dependent_products_realizability.
    - exact has_dependent_sums_realizability.
  Defined.

  (** * 6. The realizability tripos *)
  Definition is_preorder_tripos_realizability
    : is_preorder_tripos realizability_first_order_preoder_hyperdoctrine.
  Proof.
    refine (λ (X : hSet), _).
    simple refine (_ ,, _ ,, _).
    - use make_hSet.
      + exact (X → A → hProp).
      + abstract
          (do 2 use funspace_isaset ;
           apply isasethProp).
    - exact (λ xp a, pr2 xp (pr1 xp) a).
    - simple refine (λ (X' : hSet) (Φ : X × X' → A → hProp), _ ,, _).
      + exact (λ x' x a, Φ (x ,, x') a).
      + abstract
          (cbn ;
           use funextsec ; intros ( x & x' ) ;
           use funextsec ; intro a ;
           apply idpath).
  Defined.
  
  Definition realizability_preorder_tripos
    : preorder_tripos.
  Proof.
    simple refine (_ ,, _).
    - exact realizability_first_order_preoder_hyperdoctrine.
    - exact is_preorder_tripos_realizability.
  Defined.
End RealizabilityTripos.
