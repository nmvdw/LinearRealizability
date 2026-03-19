Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Require Import SplitFibration.SplitDispSetCat.

Local Open Scope cat.

Definition terminal_disp_cat
           (C : category)
  : disp_cat C
  := disp_full_sub C (λ _, htrue).

Proposition is_univalent_terminal_disp_cat
            (C : category)
  : is_univalent_disp (terminal_disp_cat C).
Proof.
  use disp_full_sub_univalent.
  intros.
  apply propproperty.
Qed.

Definition cleaving_terminal_disp_cat
           (C : category)
  : cleaving (terminal_disp_cat C).
Proof.
  intros x y f xx.
  refine (tt ,, tt ,, _).
  intros w g ww hh.
  use make_iscontr.
  - refine (tt ,, _).
    apply isapropunit.
  - abstract
      (intro ;
       use subtypePath ; [ intro ; apply homsets_disp | ] ;
       apply isapropunit).
Defined.

Proposition is_split_cleaving_terminal_disp_cat
            (C : category)
  : is_split (cleaving_terminal_disp_cat C).
Proof.
  repeat split.
  - intro ; intros.
    simple refine (_ ,, _) ; apply isapropunit.
  - intro ; intros.
    simple refine (_ ,, _) ; apply isapropunit.
  - intro.
    apply isasetunit.
Qed.

Definition disp_functor_to_terminal_disp_cat
           {C : category}
           (D : disp_cat C)
  : disp_functor
      (functor_identity C)
      D
      (terminal_disp_cat C).
Proof.
  simple refine (_ ,, _).
  - simple refine (_ ,, _).
    + exact (λ _ _, tt).
    + exact (λ _ _ _ _ _ _, tt).
  - abstract
      (split ; intro ; intros ; apply isapropunit).
Defined.
    
Section TerminalSplitDispSetCat.
  Context (C : category).

  (** * 1. The terminal split fibration *)
  Definition terminal_split_disp_setcat
    : split_disp_setcat C.
  Proof.
    use make_split_disp_setcat.
    - exact (terminal_disp_cat C).
    - exact (cleaving_terminal_disp_cat C).
    - exact (is_split_cleaving_terminal_disp_cat C).
  Defined.

  (** * 2. The 1-categorical universal property *)
  Definition disp_functor_to_terminal_split_disp_setcat
             (D : split_disp_setcat C)
    : split_disp_functor D terminal_split_disp_setcat.
  Proof.
    use make_split_disp_functor.
    - exact (disp_functor_to_terminal_disp_cat D).
    - abstract
        (intro ; intros ;
         simple refine (_ ,, _) ; apply isapropunit).
  Defined.

  Proposition disp_functor_to_terminal_split_disp_setcat_unique
              {D : split_disp_setcat C}
              (FF GG : split_disp_functor D terminal_split_disp_setcat)
    : FF = GG.
  Proof.
    use split_disp_functor_eq.
    use total2_paths_f.
    - repeat (use funextsec ; intro).
      apply isapropunit.
    - repeat (use funextsec ; intro).
      apply isapropunit.
  Qed.

  Definition terminal_category_of_split_disp_setcat
    : Terminal (category_of_split_disp_setcat C).
  Proof.
    use make_Terminal.
    - exact terminal_split_disp_setcat.
    - intros D.
      use make_iscontr.
      + exact (disp_functor_to_terminal_split_disp_setcat D).
      + abstract
          (intros ;
           apply disp_functor_to_terminal_split_disp_setcat_unique).
  Defined.
  
  (** * 3. The 2-categorical universal property *)
  Definition disp_functor_to_terminal_split_disp_setcat_nat_trans
             {D : split_disp_setcat C}
             (FF GG : split_disp_functor D terminal_split_disp_setcat)
    : disp_nat_trans (nat_trans_id _) FF GG.
  Proof.
    simple refine (_ ,, _).
    - exact (λ _ _, tt).
    - abstract (intro ; intros ; apply isapropunit).
  Defined.

  Proposition disp_functor_to_terminal_split_disp_setcat_nat_trans_unique
              {D : split_disp_setcat C}
              {FF GG : split_disp_functor D terminal_split_disp_setcat}
              (θ₁ θ₂ : disp_nat_trans (nat_trans_id _) FF GG)
    : θ₁ = θ₂.
  Proof.
    use disp_nat_trans_eq.
    intros.
    apply isapropunit.
  Qed.
End TerminalSplitDispSetCat.
