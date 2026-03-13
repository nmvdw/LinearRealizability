Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import InternalCategories.InternalCat.
Require Import InternalCategories.InternalFunctor.
Require Import InternalCategories.InternalNatTrans.
Require Import InternalCategories.CatOfInternalCat.

Local Open Scope cat.

Section TerminalInternalCat.
  Context {C : category}
          (T : Terminal C)
          (PB : Pullbacks C).

  (** * 1. The terminal internal category *)
  Definition terminal_internal_cat_diag
    : internal_cat_diag C.
  Proof.
    use make_internal_cat_diag.
    - exact T.
    - exact T.
    - exact (identity _).
    - exact (identity _).
  Defined.

  Definition terminal_internal_cat_id_comp
    : internal_cat_id_comp PB terminal_internal_cat_diag.
  Proof.
    split.
    - refine (identity _ ,, _ ,, _).
      + apply TerminalArrowEq.
      + apply TerminalArrowEq.
    - refine (TerminalArrow _ _ ,, _ ,, _).
      + apply TerminalArrowEq.
      + apply TerminalArrowEq.
  Defined.
  
  Definition terminal_internal_cat_data
    : internal_cat_data PB.
  Proof.
    use make_internal_cat_data.
    - exact terminal_internal_cat_diag.
    - exact terminal_internal_cat_id_comp.
  Defined.

  Proposition terminal_internal_cat_laws
    : disp_cat_axioms C (internal_cat_disp_cat_data terminal_internal_cat_data).
  Proof.
    use make_internal_cat_axioms.
    - intros.
      use internal_morphism_eq.
      apply TerminalArrowEq.
    - intros.
      use internal_morphism_eq.
      apply TerminalArrowEq.
    - intros.
      use internal_morphism_eq.
      apply TerminalArrowEq.
  Qed.
  
  Definition terminal_internal_cat
    : internal_cat PB.
  Proof.
    use make_internal_cat.
    - exact terminal_internal_cat_data.
    - exact terminal_internal_cat_laws.
  Defined.

  (** * 2. The universal property of the terminal object *)
  Definition internal_functor_to_terminal_data
             (d : internal_cat PB)
    : internal_functor_data d terminal_internal_cat.
  Proof.
    use make_internal_functor_data.
    - split.
      + apply TerminalArrow.
      + apply TerminalArrow.
    - apply TerminalArrowEq.
    - apply TerminalArrowEq.
  Defined.

  Proposition internal_functor_to_terminal_laws
              (d : internal_cat PB)
    : disp_functor_axioms
        (internal_functor_to_disp_functor_data
           (internal_functor_to_terminal_data d)).
  Proof.
    use make_internal_functor_axioms.
    - intros.
      use internal_morphism_eq.
      apply TerminalArrowEq.
    - intros.
      use internal_morphism_eq.
      apply TerminalArrowEq.
  Qed.
  
  Definition internal_functor_to_terminal
             (d : internal_cat PB)
    : internal_functor d terminal_internal_cat.
  Proof.
    use make_internal_functor.
    - exact (internal_functor_to_terminal_data d).
    - exact (internal_functor_to_terminal_laws d).
  Defined.

  Definition internal_functor_to_terminal_eq
             {d : internal_cat PB}
             (f g : internal_functor d terminal_internal_cat)
    : f = g.
  Proof.
    use internal_functor_eq.
    - apply TerminalArrowEq.
    - apply TerminalArrowEq.
  Qed.
  
  Definition terminal_cat_of_internal_cat
    : Terminal (cat_of_internal_cat PB).
  Proof.
    use make_Terminal.
    - exact terminal_internal_cat.
    - intro d.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           apply internal_functor_to_terminal_eq).
      + exact (internal_functor_to_terminal d).
  Defined.

  (** * 3. Natural transformations to functors into the terminal object *)
  Definition internal_functor_to_terminal_nat_trans
             {d : internal_cat PB}
             (f g : internal_functor d terminal_internal_cat)
    : internal_nat_trans f g.
  Proof.
    use make_internal_nat_trans.
    - use make_internal_nat_trans_data.
      + apply TerminalArrow.
      + apply TerminalArrowEq.
      + apply TerminalArrowEq.
    - abstract
        (use make_internal_nat_trans_laws ;
         intros ;
         use internal_morphism_eq ;
         apply TerminalArrowEq).
  Defined.

  Definition internal_functor_to_terminal_nat_trans_eq
             {d : internal_cat PB}
             {f g : internal_functor d terminal_internal_cat}
             (θ₁ θ₂ : internal_nat_trans f g )
    : θ₁ = θ₂.
  Proof.
    use internal_nat_trans_eq.
    apply TerminalArrowEq.
  Qed.
End TerminalInternalCat.
