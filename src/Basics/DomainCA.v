(**

 Every reflexive object gives rise to a combinatory algebra

 We show that every reflexive object `x` in a Cartesian closed category gives rise to
 a combinatory algebra whose carrier consists of morphisms `w --> x`. This construction
 can be applied to, for instance, Scott's `D_∞` to obtain a combinatory algebra. 

 Content
 1. Reflexive objects to combinatory algebras
 1.1. Application
 1.2. K-combinator
 1.3. S-combinator
 1.4. The combinatory algebra arising from a reflexive object
 2. Extensional combinatory algebras from reflexive objects with an isomorphism
 3. The combinatory algebra arising from a reflexive DCPO
 4. Points in that combinatory algebra

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.DCPOStructures.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.Posets.PointedPosets.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Core.ScottContinuous.
Require Import UniMath.OrderTheory.DCPOs.Examples.Unit.
Require Import UniMath.OrderTheory.DCPOs.Examples.Exponentials.

Require Import Basics.CombinatoryAlgebra.

Local Open Scope cat.

(** * 1. Reflexive objects to combinatory algebras *)
Section ReflexiveObject.
  Context {D : category}
          {BP : BinProducts D}
          {expD : Exponentials BP}
          (w : D)
          {x : D}
          (retr : retraction (exp (expD x) x) x).

  Let s : exp (expD x) x --> x := retraction_section retr.
  Let r : x --> exp (expD x) x := retraction_retraction retr.

  (** * 1.1. Application *)
  Definition reflexive_object_app
             (f g : w --> x)
    : w --> x.
  Proof.
    refine (_ · exp_eval (expD x) x).
    use BinProductArrow.
    - exact g.
    - exact (f · r).
  Defined.

  Arguments reflexive_object_app /.
  
  Definition reflexive_object_to_applicative_structure
    : applicative_structure.
  Proof.
    use make_applicative_structure.
    - exact (homset w x).
    - exact reflexive_object_app.
  Defined.

  (** * 1.2. K-combinator *)
  Definition reflexive_object_K
    : w --> x.
  Proof.
    refine (exp_lam _ _ · s).
    refine (exp_lam _ _ · s).
    exact (BinProductPr2 _ _ · BinProductPr1 _ _).
  Defined.

  Arguments reflexive_object_K /.

  Proposition reflexive_object_K_eq
              (f g : w --> x)
    : reflexive_object_app (reflexive_object_app reflexive_object_K f) g = f.
  Proof.
    cbn.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply retraction_is_retraction.
    }
    rewrite id_right.
    rewrite assoc.
    rewrite <- (id_right f).
    rewrite <- (id_left (exp_lam _ _)).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths_2.
      refine (!_).
      use postcompWithBinProductArrow.
      apply BP.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      rewrite assoc.
      rewrite exp_beta.
      rewrite assoc'.
      apply maponpaths.
      apply retraction_is_retraction.
    }
    rewrite id_right.
    rewrite <- (id_right g).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      use postcompWithBinProductArrow.
      apply BP.
    }
    rewrite !assoc'.
    rewrite exp_beta.
    rewrite !assoc.
    rewrite BinProductPr2Commutes.
    rewrite BinProductPr1Commutes.
    rewrite id_right.
    apply idpath.
  Qed.

  (** * 1.3. S-combinator *)
  Definition reflexive_object_S
    : w --> x.
  Proof.
    refine (exp_lam _ _ · s).
    refine (exp_lam _ _ · s).
    refine (exp_lam _ _ · s).
    refine (_ · exp_eval (expD x) x).
    use BinProductArrow.
    - refine (_ · exp_eval (expD x) x).
      use BinProductArrow.
      + exact (BinProductPr1 _ _).
      + exact (BinProductPr2 _ _ · BinProductPr1 _ _ · r).
    - refine (_ · r).
      refine (_ · exp_eval (expD x) x).
      use BinProductArrow.
      + exact (BinProductPr1 _ _).
      + exact (BinProductPr2 _ _ · BinProductPr2 _ _ · BinProductPr1 _ _ · r).
  Defined.

  Arguments reflexive_object_S /.

  Proposition reflexive_object_S_eq
              (f g h : w --> x)
    : reflexive_object_app
        (reflexive_object_app
           (reflexive_object_app
              reflexive_object_S
              f)
           g)
        h
      =
      reflexive_object_app
        (reflexive_object_app f h)
        (reflexive_object_app g h).
  Proof.
    cbn.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        rewrite assoc'.
        apply maponpaths.
        apply retraction_is_retraction.
      }
      rewrite id_right.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          exact (!(id_right f)).
        }
        apply maponpaths.
        exact (!(id_left (exp_lam _ _))).
      }
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        use postcompWithBinProductArrow.
        apply BP.
      }
      rewrite !assoc'.
      rewrite exp_beta.
      apply idpath.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      do 3 apply maponpaths.
      apply retraction_is_retraction.
    }
    rewrite id_right.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.        
        etrans.
        {
          apply maponpaths_2.
          exact (!(id_right g)).
        }
        refine (!_).
        use postcompWithBinProductArrow.
        apply BP.
      }
      rewrite !assoc'.
      rewrite exp_beta.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      rewrite !assoc'.
      do 2 apply maponpaths.
      apply retraction_is_retraction.
    }
    rewrite id_right.
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (!(id_right h)).
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      use postcompWithBinProductArrow.
      apply BP.
    }
    rewrite assoc'.
    rewrite exp_beta.
    rewrite !assoc.
    apply maponpaths_2.
    use BinProductArrowUnique.
    - rewrite !assoc'.
      rewrite BinProductPr1Commutes.
      rewrite !assoc.
      apply maponpaths_2.
      use BinProductArrowUnique.
      + rewrite !assoc'.
        rewrite !BinProductPr1Commutes.
        apply idpath.
      + rewrite !assoc'.
        rewrite BinProductPr2Commutes.
        rewrite !assoc.
        rewrite BinProductPr2Commutes.
        rewrite BinProductPr1Commutes.
        apply idpath.
    - rewrite !assoc'.
      rewrite BinProductPr2Commutes.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      use BinProductArrowUnique.
      + rewrite !assoc'.
        rewrite BinProductPr1Commutes.
        rewrite BinProductPr1Commutes.
        apply idpath.
      + rewrite !assoc'.
        rewrite BinProductPr2Commutes.
        rewrite !assoc.
        rewrite !BinProductPr2Commutes.
        rewrite BinProductPr1Commutes.
        apply idpath.
  Qed.

  (** * 1.4. The combinatory algebra arising from a reflexive object *)
  Definition reflexive_object_to_combinatory_algebra_obj
    : combinatory_algebra.
  Proof.
    use make_combinatory_algebra.
    - exact reflexive_object_to_applicative_structure.
    - exact reflexive_object_K.
    - exact reflexive_object_S.
    - exact reflexive_object_K_eq.
    - exact reflexive_object_S_eq.
  Defined.
End ReflexiveObject.

Definition reflexive_object_to_combinatory_algebra
           {D : category}
           {BP : BinProducts D}
           {expD : Exponentials BP}
           (term : Terminal D)
           {x : D}
           (retr : retraction (exp (expD x) x) x)
  : combinatory_algebra
  := reflexive_object_to_combinatory_algebra_obj term retr.

(** * 2. Extensional combinatory algebras from reflexive objects with an isomorphism *)
Proposition reflexive_object_z_iso_to_combinatory_algebra_ext
            {D : category}
            {BP : BinProducts D}
            {expD : Exponentials BP}
            (term : Terminal D)
            {x : D}
            (retr : retraction (exp (expD x) x) x)
            (H : enough_points term)
            (H' : is_z_isomorphism (retraction_retraction retr))
  : is_extensional_applicative_structure
      (reflexive_object_to_combinatory_algebra term retr).
Proof.
  intros f g p.
  cbn in *.
  unfold reflexive_object_app in p ; cbn in p.
  refine (!(id_right _) @ _ @ id_right _).
  rewrite <- (z_iso_inv_after_z_iso (_ ,, H')) ; cbn.
  rewrite !assoc.
  apply maponpaths_2.
  use exp_funext.
  intros a h.
  use H.
  intros pt.
  specialize (p (pt · BinProductPr1 _ _ · h)).
  refine (_ @ p @ _).
  - rewrite !assoc.
    apply maponpaths_2.
    unfold BinProductOfArrows.
    rewrite precompWithBinProductArrow.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply TerminalArrowEq.
  - rewrite !assoc.
    apply maponpaths_2.
    unfold BinProductOfArrows.
    rewrite precompWithBinProductArrow.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!(id_left _) @ _).
    apply maponpaths_2.
    apply TerminalArrowEq.
Qed.

Section ReflexiveDCPO.
  Context (D : dcpo)
          (s : scott_continuous_map (dcpo_funspace D D) D)
          (r : scott_continuous_map D (dcpo_funspace D D))
          (p : ∏ (f : dcpo_funspace D D), r(s f) = f).

  (** * 3. The combinatory algebra arising from a reflexive DCPO *)
  Definition reflexive_dcpo_to_combinatory_algebra
    : combinatory_algebra.
  Proof.
    use reflexive_object_to_combinatory_algebra.
    - exact DCPO.
    - exact BinProducts_DCPO.
    - exact Exponentials_DCPO.
    - exact Terminal_DCPO.
    - exact D.
    - use make_retraction.
      + exact s.
      + exact r.
      + abstract
          (use subtypePath ;
           [ intro ; apply isaprop_is_scott_continuous
           | ] ;
           cbn ;
           use funextsec ;
           exact p).
  Defined.

  Proposition is_extensional_reflexive_dcpo_to_combinatory_algebra
              (q : ∏ (d : D), s(r d) = d)
    : is_extensional_applicative_structure
        reflexive_dcpo_to_combinatory_algebra.
  Proof.
    use reflexive_object_z_iso_to_combinatory_algebra_ext.
    - exact enough_points_Terminal_DCPO.
    - cbn.
      use make_is_z_isomorphism.
      + exact s.
      + split.
        * use subtypePath.
          {
            intro.
            apply isaprop_is_scott_continuous.
          }
          use funextsec.
          intro.
          cbn.
          apply q.
        * use subtypePath.
          {
            intro.
            apply isaprop_is_scott_continuous.
          }
          use funextsec.
          intro.
          cbn.
          apply p.
  Qed.

  (** * 4. Points in that combinatory algebra *)
  Definition el_to_reflexive_dcpo_to_ca
             (d : D)
    : reflexive_dcpo_to_combinatory_algebra.
  Proof.
    refine ((λ _, d) ,, _).
    apply is_scott_continuous_constant.
  Defined.

  Definition reflexive_dcpo_to_ca_to_el
             (d : reflexive_dcpo_to_combinatory_algebra)
    : D
    := pr1 d tt.

  Proposition reflexive_dcpo_to_ca_to_el_eq
              (d : reflexive_dcpo_to_combinatory_algebra)
    : el_to_reflexive_dcpo_to_ca
        (reflexive_dcpo_to_ca_to_el d)
      =
      d.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_scott_continuous.
    }
    use funextsec.
    intro z.
    induction z.
    cbn.
    apply idpath.
  Qed.
  
  Definition map_to_reflexive_dcpo_to_ca
             (f : scott_continuous_map D D)
    : reflexive_dcpo_to_combinatory_algebra.
  Proof.
    refine ((λ _, (s f)) ,, _).
    apply is_scott_continuous_constant.
  Defined.

  Proposition app_reflexive_dcpo_to_combinatory_algebra
              (f : scott_continuous_map D D)
              (d : reflexive_dcpo_to_combinatory_algebra)
    : (map_to_reflexive_dcpo_to_ca f · d)%ca
      =
      el_to_reflexive_dcpo_to_ca (f (reflexive_dcpo_to_ca_to_el d)).
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_scott_continuous.
    }
    use funextsec.
    intro z.
    induction z.
    cbn.
    exact (maponpaths (λ (h : scott_continuous_map _ _), h (pr1 d tt)) (p f)).
  Qed.

  Proposition app_reflexive_dcpo_to_combinatory_algebra_el
              (f : scott_continuous_map D D)
              (d : D)
    : (map_to_reflexive_dcpo_to_ca f · el_to_reflexive_dcpo_to_ca d)%ca
      =
      el_to_reflexive_dcpo_to_ca (f d).
  Proof.
    apply app_reflexive_dcpo_to_combinatory_algebra.
  Qed.
End ReflexiveDCPO.
