Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.TwoCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.PreservesCleaving.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.

Require Import SplitFibration.SplitDispSetCat.

Local Open Scope cat.

Section TwoCatOfSetDispCat.
  Context (C : category).

  (** * 1. The 2-category of split fibrations over a fixed category *)
  Definition two_cat_data_of_split_disp_setcat
    : two_cat_data.
  Proof.
    use make_two_cat_data.
    - exact (category_of_split_disp_setcat C).
    - exact (λ _ _ (F G : split_disp_functor _ _),
             disp_nat_trans
               (nat_trans_id _)
               F
               G).
    - exact (λ _ _ _, disp_nat_trans_id _).
    - exact (λ _ _ _ _ _ α β, disp_nat_trans_over_id_comp α β).
    - exact (λ _ _ _ _ _ _ α, disp_nat_trans_over_id_prewhisker _ α).
    - exact (λ _ _ _ _ _ _ α, disp_nat_trans_over_id_postwhisker _ α).
  Defined.

  
  Definition two_cat_category_of_split_disp_setcat
    : two_cat_category.
  Proof.
    use make_two_cat_category.
    - exact two_cat_data_of_split_disp_setcat.
    - exact (pr21 (category_of_split_disp_setcat C)).
    - abstract
        (intros D₁ D₂ ;
         apply isaset_split_disp_functor).
  Defined.

  Proposition idto2mor_two_cat_category_of_split_disp_set_cat_help
              {D₁ D₂ : split_disp_setcat C}
              {FF GG : split_disp_functor D₁ D₂}
              (p : FF = GG)
              {x : C}
              (xx : D₁ x)
    : pr1 (idto2mor (C := two_cat_data_of_split_disp_setcat) p) x xx
      =
      transportf
        (λ (z : disp_functor_data (functor_identity _) D₁ D₂), _ -->[ _ ] z x xx)
        (maponpaths (λ z, pr11 z) p)
        (id_disp _).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.
  
  Proposition idto2mor_two_cat_category_of_split_disp_setcat
              {D₁ D₂ : split_disp_setcat C}
              {F : disp_functor_data (functor_identity _) D₁ D₂}
              {HF₁ HG₁ : disp_functor_axioms F}
              (FF' := F ,, HF₁ : disp_functor _ _ _)
              (GG' := F ,, HG₁ : disp_functor _ _ _)
              (HF₂ : preserves_cleaving D₁ D₂ FF')
              (HG₂ : preserves_cleaving D₁ D₂ GG')
              (FF := FF' ,, HF₂ : split_disp_functor _ _)
              (GG := GG' ,, HG₂ : split_disp_functor _ _)
              (p : FF = GG)
              {x : C}
              (xx : D₁ x)
    : pr1 (idto2mor (C := two_cat_data_of_split_disp_setcat) p) x xx = id_disp _.
  Proof.
    etrans.
    {
      apply idto2mor_two_cat_category_of_split_disp_set_cat_help.
    }
    cbn.
    rewrite transportf_set ; [ apply idpath | ].
    use isaset_total2.
    - do 2 (use impred_isaset ; intro).
      apply isaset_split_disp_ob.
    - intro.
      do 6 (use impred_isaset ; intro).
      apply homsets_disp.
  Qed.

  Proposition two_cat_laws_of_split_disp_setcat
    : two_cat_laws two_cat_category_of_split_disp_setcat.
  Proof.
    repeat split.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      rewrite mor_disp_transportf_prewhisker, mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      apply idpath.
    - intros D₁ D₂ D₃ F G ; use disp_nat_trans_eq ; intros ; cbn.
      refine (disp_functor_id (split_disp_functor_to_disp_functor G) _ @ _).
      apply transportf_set.
      apply homset_property.
    - intro ; intros ; use disp_nat_trans_eq ; intros ; cbn.
      apply idpath.
    - intros D₁ D₂ D₃ F₁ F₂ F₃ F₄ τ₁ τ₂.
      use disp_nat_trans_eq ; intros ; cbn.
      rewrite (disp_functor_transportf _ (pr1 F₄)).
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ F₁ F₂ F₃ F₄ τ₁ τ₂.
      use disp_nat_trans_eq ; intros ; cbn.
      etrans.
      {
        apply maponpaths.
        apply (disp_nat_trans_ax τ₂).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ F G τ.
      use disp_nat_trans_eq ; intros ; cbn.
      etrans.
      {
        do 2 apply maponpaths.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (id_left G) xx).
      }
      rewrite id_right_disp.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (id_left F) xx).
      }
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ F G τ.
      use disp_nat_trans_eq ; intros ; cbn.
      etrans.
      {
        do 2 apply maponpaths.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (id_right G) xx).
      }
      rewrite id_right_disp.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (id_right F) xx).
      }
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ D₄ F₁ F₂ F₃ F₄ τ.
      use disp_nat_trans_eq ; intros ; cbn.
      etrans.
      {
        do 2 apply maponpaths.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (assoc F₁ F₂ F₄) xx).
      }
      rewrite id_right_disp.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (assoc F₁ F₂ F₃) xx).
      }
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ D₄ F₁ F₂ F₃ F₄ τ.
      use disp_nat_trans_eq ; intros ; cbn.
      etrans.
      {
        do 2 apply maponpaths.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (assoc F₁ F₃ F₄) xx).
      }
      rewrite id_right_disp.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (assoc F₁ F₂ F₄) xx).
      }
      rewrite id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ D₄ F₁ F₂ F₃ F₄ τ.
      use disp_nat_trans_eq ; intros ; cbn.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (assoc F₁ F₃ F₄) xx).
      }
      rewrite id_left_disp.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (idto2mor_two_cat_category_of_split_disp_setcat _ _ (assoc F₂ F₃ F₄) xx).
      }
      rewrite id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition two_precat_of_split_disp_setcat
    : two_precat.
  Proof.
    use make_two_precat.
    - exact two_cat_category_of_split_disp_setcat.
    - exact two_cat_laws_of_split_disp_setcat.
  Defined.
  
  Definition two_cat_of_split_disp_setcat
    : two_cat.
  Proof.
    use make_two_cat.
    - exact two_precat_of_split_disp_setcat.
    - abstract
        (intro ; intros ;
         apply isaset_disp_nat_trans).
  Defined.

  (** * 2. This 2-category is univalent *)
  Definition univalent_twqo_cat_of_split_disp_setcat
    : univalent_two_cat.
  Proof.
    use make_univalent_two_cat.
    - exact two_cat_of_split_disp_setcat.
    - exact (is_univalent_category_of_split_disp_setcat C).
  Defined.
End TwoCatOfSetDispCat.
