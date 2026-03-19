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
Require Import UniMath.CategoryTheory.Limits.BinProducts.

Require Import SplitFibration.SplitDispSetCat.

Local Open Scope cat.

Proposition idtoiso_disp_dirprod_disp_cat_pr1
            {C : category}
            {D₁ D₂ : disp_cat C}
            {x : C}
            {xx yy : D₁ x × D₂ x}
            (q : xx = yy)
  : pr11 (idtoiso_disp (D := dirprod_disp_cat D₁ D₂) (idpath _) q)
    =
    idtoiso_disp (D := D₁) (idpath _) (maponpaths dirprod_pr1 q).
Proof.
  induction q ; cbn.
  apply idpath.
Qed.

Proposition idtoiso_disp_dirprod_disp_cat_pr2
            {C : category}
            {D₁ D₂ : disp_cat C}
            {x : C}
            {xx yy : D₁ x × D₂ x}
            (q : xx = yy)
  : pr21 (idtoiso_disp (D := dirprod_disp_cat D₁ D₂) (idpath _) q)
    =
    idtoiso_disp (D := D₂) (idpath _) (maponpaths dirprod_pr2 q).
Proof.
  induction q ; cbn.
  apply idpath.
Qed.

Section CleavingDirprod.
  Context {C : category}
          {D₁ D₂ : disp_cat C}
          (HD₁ : cleaving D₁)
          (HD₂ : cleaving D₂).

  Section CartesianLift.
    Context {x y : C}
            (f : y --> x)
            (xx : (dirprod_disp_cat D₁ D₂) x).

    Definition cleaving_dirprod_disp_cat_ob
      : (dirprod_disp_cat D₁ D₂) y.
    Proof.
      simple refine (_ ,, _).
      - exact (HD₁ x y f (pr1 xx)).
      - exact (HD₂ x y f (pr2 xx)).
    Defined.

    Definition cleaving_dirprod_disp_cat_mor
      : cleaving_dirprod_disp_cat_ob -->[ f ] xx.
    Proof.
      simple refine (_ ,, _).
      - exact (HD₁ x y f (pr1 xx)).
      - exact (HD₂ x y f (pr2 xx)).
    Defined.

    Proposition is_cartesian_cleaving_dirprod_disp_cat_mor
      : is_cartesian cleaving_dirprod_disp_cat_mor.
    Proof.
      intros w g ww hh.
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply homsets_disp | ] ;
           use pathsdirprod ;
           [ use (cartesian_factorisation_unique (HD₁ x y f (pr1 xx))) ;
             exact (maponpaths dirprod_pr1 (pr2 φ₁ @ !(pr2 φ₂)))
           | ] ;
           use (cartesian_factorisation_unique (HD₂ x y f (pr2 xx))) ;
           exact (maponpaths dirprod_pr2 (pr2 φ₁ @ !(pr2 φ₂)))).
      - simple refine (_ ,, _).
        + simple refine (_ ,, _).
          * use (cartesian_factorisation (HD₁ x y f (pr1 xx))).
            exact (pr1 hh).
          * use (cartesian_factorisation (HD₂ x y f (pr2 xx))).
            exact (pr2 hh).
        + abstract
            (cbn ;
             use pathsdirprod ;
             apply cartesian_factorisation_commutes).
    Defined.
  End CartesianLift.
  
  Definition cleaving_dirprod_disp_cat         
    : cleaving (dirprod_disp_cat D₁ D₂).
  Proof.
    intros x y f xx.
    simple refine (_ ,, _ ,, _).
    - exact (cleaving_dirprod_disp_cat_ob f xx).
    - exact (cleaving_dirprod_disp_cat_mor f xx).
    - exact (is_cartesian_cleaving_dirprod_disp_cat_mor f xx).
  Defined.

  Proposition is_split_cleaving_dirprod_disp_cat
              (H₁ : is_split HD₁)
              (H₂ : is_split HD₂)
    : is_split cleaving_dirprod_disp_cat.
  Proof.
    repeat split.
    - intros x xx.
      simple refine (_ ,, _).
      + use pathsdirprod.
        * exact (pr1 (pr1 H₁ x (pr1 xx))).
        * exact (pr1 (pr1 H₂ x (pr2 xx))).
      + cbn.
        use dirprod_paths.
        * refine (pr2 (pr1 H₁ x (pr1 xx)) @ _).
          unfold transportb ; cbn.
          refine (!_).
          refine (pr1_transportf (!(pathsdirprod _ _)) _ @ _).
          etrans.
          {
            apply (functtransportf
                     dirprod_pr1
                     (λ z, z -->[ _ ] _)
                     (!(pathsdirprod _ _))).
          }
          apply maponpaths_2.
          rewrite maponpathsinv0.
          rewrite maponpaths_pr1_pathsdirprod.
          apply idpath.
        * refine (pr2 (pr1 H₂ x (pr2 xx)) @ _).
          unfold transportb ; cbn.
          refine (!_).
          etrans.
          {
            apply (pr2_transportf
                     (B1 := λ z, pr1 z -->[ _ ] _)
                     (B2 := λ z, pr2 z -->[ _ ] _)
                     (!(pathsdirprod _ _))).
          }
          etrans.
          {
            apply (functtransportf
                     dirprod_pr2
                     (λ z, z -->[ _ ] _)
                     (!(pathsdirprod _ _))).
          }
          apply maponpaths_2.
          rewrite maponpathsinv0.
          rewrite maponpaths_pr2_pathsdirprod.
          apply idpath.
    - intros x y z f g zz.
      simple refine (_ ,, _).
      + use pathsdirprod.
        * exact (pr1 (pr12 H₁ _ _ _ _ _ (pr1 zz))).
        * exact (pr1 (pr12 H₂ _ _ _ _ _ (pr2 zz))).
      + cbn.
        use dirprod_paths.
        * refine (pr2 (pr12 H₁ _ _ _ _ _ (pr1 zz)) @ _).
          unfold transportb ; cbn.
          refine (!_).
          refine (pr1_transportf (!(pathsdirprod _ _)) _ @ _).
          etrans.
          {
            apply (functtransportf
                     dirprod_pr1
                     (λ z, z -->[ _ ] _)
                     (!(pathsdirprod _ _))).
          }
          apply maponpaths_2.
          rewrite maponpathsinv0.
          rewrite maponpaths_pr1_pathsdirprod.
          apply idpath.
        * refine (pr2 (pr12 H₂ _ _ _ _ _ (pr2 zz)) @ _).
          unfold transportb ; cbn.
          refine (!_).
          etrans.
          {
            apply (pr2_transportf
                     (B1 := λ z, pr1 z -->[ _ ] _)
                     (B2 := λ z, pr2 z -->[ _ ] _)
                     (!(pathsdirprod _ _))).
          }
          etrans.
          {
            apply (functtransportf
                     dirprod_pr2
                     (λ z, z -->[ _ ] _)
                     (!(pathsdirprod _ _))).
          }
          apply maponpaths_2.
          rewrite maponpathsinv0.
          rewrite maponpaths_pr2_pathsdirprod.
          apply idpath.
    - intro x.
      apply isaset_dirprod.
      + apply H₁.
      + apply H₂.
  Qed.
End CleavingDirprod.

Section PairDispFunctor.
  Context {C : category}
          {D₁ D₂ E : disp_cat C}
          (FF : disp_functor (functor_identity _) E D₁)
          (GG : disp_functor (functor_identity _) E D₂).

  Definition prod_disp_functor_data
    : disp_functor_data (functor_identity _) E (dirprod_disp_cat D₁ D₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, FF x xx ,, GG x xx).
    - exact (λ x y xx yy f ff, ♯FF ff ,, ♯GG ff)%mor_disp.
  Defined.

  Proposition prod_disp_functor_axioms
    : disp_functor_axioms prod_disp_functor_data.
  Proof.
    split.
    - intros x xx ; cbn.
      use pathsdirprod.
      + apply (disp_functor_id FF).
      + apply (disp_functor_id GG).
    - intros x y z xx yy zz f g ff gg ; cbn.
      use pathsdirprod.
      + apply (disp_functor_comp FF).
      + apply (disp_functor_comp GG).
  Qed.

  Definition prod_disp_functor
    : disp_functor (functor_identity _) E (dirprod_disp_cat D₁ D₂).
  Proof.
    simple refine (_ ,, _).
    - exact prod_disp_functor_data.
    - exact prod_disp_functor_axioms.
  Defined.

  Proposition preserves_cleaving_prod_disp_functor
              {HD₁ : cleaving D₁}
              {HD₂ : cleaving D₂}
              {HE : cleaving E}
              (HFF : preserves_cleaving HE HD₁ FF)
              (HGG : preserves_cleaving HE HD₂ GG)
    : preserves_cleaving HE (cleaving_dirprod_disp_cat HD₁ HD₂) prod_disp_functor.
  Proof.
    intros x y f yy ; cbn -[idtoiso_disp].
    simple refine (_ ,, _).
    - use pathsdirprod.
      + apply HFF.
      + apply HGG.
    - use dirprod_paths.
      + refine (pr1_transportf _ _ @ _).
        refine (pr2 (HFF x y f yy) @ _).
        cbn -[idtoiso_disp].
        apply maponpaths_2.
        refine (!_).
        refine (idtoiso_disp_dirprod_disp_cat_pr1 (pathsdirprod _ _) @ _).
        rewrite maponpaths_pr1_pathsdirprod.
        apply idpath.
      + refine (pr2_transportf _ _ @ _).
        refine (pr2 (HGG x y f yy) @ _).
        cbn -[idtoiso_disp].
        apply maponpaths_2.
        refine (!_).
        refine (idtoiso_disp_dirprod_disp_cat_pr2 (pathsdirprod _ _) @ _).
        rewrite maponpaths_pr2_pathsdirprod.
        apply idpath.
  Qed.
End PairDispFunctor.
  
Section ProdSplitDispCat.
  Context {C : category}
          (D₁ D₂ : split_disp_setcat C).

  (** * 1. The binary product of split fibrations *)
  Definition prod_split_disp_setcat
    : split_disp_setcat C.
  Proof.
    use make_split_disp_setcat.
    - exact (dirprod_disp_cat D₁ D₂).
    - exact (cleaving_dirprod_disp_cat D₁ D₂).
    - apply is_split_cleaving_dirprod_disp_cat ; apply is_split_split_disp_set_cat.
  Defined.

  (** * 2. The 1-categorical universal property *)
  Definition prod_split_disp_setcat_pr1
    : split_disp_functor prod_split_disp_setcat D₁.
  Proof.
    use make_split_disp_functor.
    - exact (dirprodpr1_disp_functor D₁ D₂).
    - abstract
        (intros x y f yy ;
         refine (idpath _ ,, _) ; cbn ;
         rewrite id_left_disp ;
         apply idpath).
  Defined.

  Definition prod_split_disp_setcat_pr2
    : split_disp_functor prod_split_disp_setcat D₂.
  Proof.
    use make_split_disp_functor.
    - exact (dirprodpr2_disp_functor D₁ D₂).
    - abstract
        (intros x y f yy ;
         refine (idpath _ ,, _) ; cbn ;
         rewrite id_left_disp ;
         apply idpath).
  Defined.

  Definition prod_split_disp_functor
             {E : split_disp_setcat C}
             (FF : split_disp_functor E D₁)
             (GG : split_disp_functor E D₂)
    : split_disp_functor E prod_split_disp_setcat.
  Proof.
    use make_split_disp_functor.
    - exact (prod_disp_functor FF GG).
    - abstract
        (apply preserves_cleaving_prod_disp_functor ;
         apply split_disp_functor_preserves_cleaving).
  Defined.

  Proposition prod_split_disp_functor_pr1
              {E : split_disp_setcat C}
              (FF : split_disp_functor E D₁)
              (GG : split_disp_functor E D₂)
    : prod_split_disp_functor FF GG · prod_split_disp_setcat_pr1
      =
      FF.
  Proof.
    use split_disp_functor_eq.
    apply idpath.
  Qed.

  Proposition prod_split_disp_functor_pr2
              {E : split_disp_setcat C}
              (FF : split_disp_functor E D₁)
              (GG : split_disp_functor E D₂)
    : prod_split_disp_functor FF GG · prod_split_disp_setcat_pr2
      =
      GG.
  Proof.
    use split_disp_functor_eq.
    apply idpath.
  Qed.

  (** * 3. The 2-categorical universal property *)
  Section ProdDispNatTrans.
    Context {E : split_disp_setcat C}
            {FF GG : split_disp_functor E prod_split_disp_setcat}
            (θ₁ : disp_nat_trans
                    (nat_trans_id _)
                    (FF · prod_split_disp_setcat_pr1 : split_disp_functor _ _)
                    (GG · prod_split_disp_setcat_pr1 : split_disp_functor _ _))
            (θ₂ : disp_nat_trans
                    (nat_trans_id _)
                    (FF · prod_split_disp_setcat_pr2 : split_disp_functor _ _)
                    (GG · prod_split_disp_setcat_pr2 : split_disp_functor _ _)).

    Definition prod_split_disp_nat_trans   
      : disp_nat_trans (nat_trans_id _) FF GG.
    Proof.
      simple refine (_ ,, _).
      - exact (λ x xx, θ₁ x xx ,, θ₂ x xx).
      - abstract
          (intros x y f xx yy ff ;
           unfold transportb ;
           use dirprod_paths ;
           [ refine (disp_nat_trans_ax θ₁ ff @ _) ;
             refine (!_) ;
             refine (pr1_transportf _ _ @ _) ;
             apply idpath
           | ] ;
           refine (disp_nat_trans_ax θ₂ ff @ _) ;
           refine (!_) ;
           refine (pr2_transportf _ _ @ _) ;
           apply idpath).
    Defined.

    Proposition prod_split_disp_nat_trans_pr1
      : disp_nat_trans_over_id_postwhisker
          prod_split_disp_setcat_pr1
          prod_split_disp_nat_trans
        =
        θ₁.
    Proof.
      use disp_nat_trans_eq.
      intros ; cbn.
      apply idpath.
    Qed.

    Proposition prod_split_disp_nat_trans_pr2
      : disp_nat_trans_over_id_postwhisker
          prod_split_disp_setcat_pr2
          prod_split_disp_nat_trans
        =
        θ₂.
    Proof.
      use disp_nat_trans_eq.
      intros ; cbn.
      apply idpath.
    Qed.

    Proposition prod_split_disp_nat_trans_unique
      : isaprop
          (∑ (τ : disp_nat_trans (nat_trans_id _) FF GG),
           (disp_nat_trans_over_id_postwhisker prod_split_disp_setcat_pr1 τ = θ₁)
           ×
           (disp_nat_trans_over_id_postwhisker prod_split_disp_setcat_pr2 τ = θ₂)).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply isaset_disp_nat_trans.
      }
      use disp_nat_trans_eq.
      intros x xx.
      use dirprod_paths.
      - exact (maponpaths (λ z, pr1 z x xx) (pr12 ζ₁ @ !(pr12 ζ₂))).
      - exact (maponpaths (λ z, pr1 z x xx) (pr22 ζ₁ @ !(pr22 ζ₂))).
    Qed.
  End ProdDispNatTrans.
End ProdSplitDispCat.
