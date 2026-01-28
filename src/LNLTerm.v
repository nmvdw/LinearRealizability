Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Adjunctions.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.Semantics.LinearLogic.LinearNonLinear.

Import MonoidalNotations.

Local Open Scope cat.

Section LNLTerm.
  Context {𝕃 : linear_non_linear_model}
          {x : 𝕃}.

  Let L : strong_monoidal_functor (cartesian_cat_from_linear_non_linear_model 𝕃) 𝕃.
  Proof.
    refine (left_adjoint (adjunction_from_linear_non_linear_model 𝕃) ,, _).
    use is_strong_left_adjoint.
    exact (sym_monoidal_adjunction_from_linear_non_linear_model 𝕃).
  Defined.

  Let R : 𝕃 ⟶ cartesian_cat_from_linear_non_linear_model 𝕃
    := right_adjoint (adjunction_from_linear_non_linear_model 𝕃).
  
  Definition bang_modality_tm
             (f : I_{𝕃} --> x)
    : I_{𝕃} --> bang_modality 𝕃 x.
  Proof.
    refine (mon_functor_unit L · _).
    refine (#L _).
    refine (unit_from_left_adjoint (adjunction_from_linear_non_linear_model 𝕃) _ · _).
    refine (#R(_ · f)).
    exact (strong_functor_unit_inv L).
  Defined.

  Proposition bang_modality_tm_del
              (f : I_{𝕃} --> x)
    : bang_modality_tm f · ε (bang_modality 𝕃) x = f.
  Proof.
    unfold bang_modality_tm.
    rewrite !functor_comp.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite <- !functor_comp.
      apply (nat_trans_ax (ε (bang_modality 𝕃))).
    }
    simpl.
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.      
    pose proof (pr22 (symmetric_monoidal_comonad_extra_laws _ (bang_modality 𝕃))) as p.
    unfold is_mon_nat_trans_unitlaw in p.
    simpl in p.
    refine (_ @ p).
    clear p.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply (nat_trans_ax (ε (bang_modality 𝕃)) _ _ (strong_functor_unit_inv L)).
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    apply maponpaths.
    refine (!(functor_comp L _ _) @ _).
    apply maponpaths.
    pose proof (pr2 (monoidal_adjunit (sym_monoidal_adjunction_from_linear_non_linear_model 𝕃)))
      as p.
    unfold is_mon_nat_trans_unitlaw in p.
    cbn in p.
    rewrite id_left in p.
    etrans.
    {
      apply maponpaths_2.
      exact p.
    }
    rewrite !assoc'.
    refine (_ @ id_right _).
    apply maponpaths.
    rewrite <- functor_comp.
    refine (_ @ functor_id _ _).
    apply maponpaths.
    apply strong_functor_unit_unit_inv.
  Qed.
End LNLTerm.
