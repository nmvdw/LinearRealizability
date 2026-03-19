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
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.

Local Open Scope cat.
         
Section CatOfSplitDispSetCat.
  Context (C : category).

  (** * 1. The category of displayed setcategories over a fixed category *)
  Definition precategory_ob_mor_of_disp_setcat
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (∑ (D : disp_cat C), ∏ (x : C), isaset (D x)).
    - exact (λ D₁ D₂, disp_functor (functor_identity C) (pr1 D₁) (pr1 D₂)).
  Defined.
  
  Definition precategory_data_of_disp_setcat
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact precategory_ob_mor_of_disp_setcat.
    - exact (λ D, disp_functor_identity _).
    - exact (λ _ _ _ F G, disp_functor_composite F G).
  Defined.

  Proposition precategory_laws_of_disp_setcat
    : is_precategory precategory_data_of_disp_setcat.
  Proof.
    use make_is_precategory_one_assoc.
    - cbn ; intros D₁ D₂ F.
      use disp_functor_eq ; cbn.
      apply idpath.
    - cbn ; intros D₁ D₂ F.
      use disp_functor_eq ; cbn.
      apply idpath.
    - cbn ; intros D₁ D₂ D₃ D₄ F₁ F₂ F₃.
      use disp_functor_eq ; cbn.
      apply idpath.
  Qed.
  
  Definition precategory_of_disp_setcat
    : precategory.
  Proof.
    use make_precategory.
    - exact precategory_data_of_disp_setcat.
    - exact precategory_laws_of_disp_setcat.
  Defined.

  Proposition has_homsets_category_of_disp_setcat
    : has_homsets precategory_of_disp_setcat.
  Proof.
    intros D₁ D₂.
    use isaset_total2.
    - use isaset_total2.
      + do 2 (use impred_isaset ; intro).
        apply D₂.
      + intro.
        do 6 (use impred_isaset ; intro).
        apply homsets_disp.
    - intro.
      apply isasetaprop.
      apply isaprop_disp_functor_axioms.
  Qed.

  Definition category_of_disp_setcat
    : category.
  Proof.
    use make_category.
    - exact precategory_of_disp_setcat.
    - exact has_homsets_category_of_disp_setcat.
  Defined.

  Proposition idtoiso_disp_disp_set_cat_refl
              {D : category_of_disp_setcat}
              {x : C}
              {xx : pr1 D x}
              (p : xx = xx)
    : pr1 (idtoiso_disp (idpath x) p) = id_disp _.
  Proof.
    enough (p = idpath _) as -> by apply idpath.
    apply D.
  Qed.
  
  (** * 2. Isomorphisms in the category of displayed setcategories *)
  Section Isos.
    Context {D₁ D₂ : category_of_disp_setcat}
            (F : disp_functor (functor_identity C) (pr1 D₁) (pr1 D₂)).

    Section ToIso.
      Context (H₁ : ∏ (x : C), isweq (F x))
              (H₂ : disp_functor_ff F).

      Let Fo (x : C) : pr1 D₁ x ≃ pr1 D₂ x := make_weq _ (H₁ x).

      Definition weq_and_ff_to_z_iso_disp_setcat_inv_data
        : disp_functor_data (functor_identity _) (pr1 D₂) (pr1 D₁).
      Proof.
        simple refine (_ ,, _).
        - exact (λ x xx, invmap (Fo x) xx).
        - refine (λ x y xx yy f ff,
                  disp_functor_ff_inv
                    F
                    H₂
                    (transportb
                       (λ z, _ -->[ z ] _)
                       _
                       (idtoiso_disp (idpath _) _
                        ;; ff
                        ;; idtoiso_disp (idpath _) _)%mor_disp)).
          + abstract
              (cbn ;
               rewrite id_left, id_right ;
               apply idpath).
          + exact (homotweqinvweq (Fo x) xx).
          + exact (!(homotweqinvweq (Fo y) yy)).
      Defined.

      Proposition weq_and_ff_to_z_iso_disp_setcat_inv_laws
        : disp_functor_axioms weq_and_ff_to_z_iso_disp_setcat_inv_data.
      Proof.
        split.
        - intros x xx.
          cbn -[idtoiso_disp].
          refine (_ @ disp_functor_ff_inv_identity F H₂ _).
          refine (maponpaths (disp_functor_ff_inv F H₂) _).
          unfold transportb.
          rewrite (id_right_disp (D := pr1 D₂)).
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite transport_f_f.
          rewrite transportf_set ; [ | apply homset_property ].
          etrans.
          {
            apply maponpaths.
            apply (idtoiso_disp_comp (D := pr1 D₂)).
          }
          unfold transportb.
          rewrite transport_f_f.
          rewrite transportf_set ; [ | apply homset_property ].
          rewrite pathsinv0r.
          apply idpath.
        - intros x y z xx yy zz f g ff gg ; cbn -[idtoiso_disp].
          refine (_ @ disp_functor_ff_inv_compose F H₂ _ _).
          apply maponpaths.
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite mor_disp_transportf_prewhisker.
          rewrite !transport_f_f.
          rewrite !(assoc_disp_var (D := pr1 D₂)).
          rewrite !mor_disp_transportf_prewhisker.
          rewrite !transport_f_f.
          refine (!_).
          etrans.
          {
            do 3 apply maponpaths.
            rewrite assoc_disp.
            apply maponpaths.
            apply maponpaths_2.
            etrans.
            {
              apply (idtoiso_disp_comp (D := pr1 D₂)).
            }
            rewrite pathsinv0l ; cbn.
            apply idpath.
          }
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite !mor_disp_transportf_prewhisker.
          rewrite !transport_f_f.
          rewrite (id_left_disp (D := pr1 D₂)).
          unfold transportb.
          rewrite !mor_disp_transportf_prewhisker.
          rewrite transport_f_f.
          apply maponpaths_2.
          apply homset_property.
      Qed.
      
      Definition weq_and_ff_to_z_iso_disp_setcat_inv
        : disp_functor (functor_identity C) (pr1 D₂) (pr1 D₁).
      Proof.
        simple refine (_ ,, _).
        - exact weq_and_ff_to_z_iso_disp_setcat_inv_data.
        - exact weq_and_ff_to_z_iso_disp_setcat_inv_laws.
      Defined.

      Proposition weq_and_ff_to_z_iso_disp_setcat_inv_left
        : disp_functor_composite_data weq_and_ff_to_z_iso_disp_setcat_inv F
          =
          pr1 (disp_functor_identity _).
      Proof.
        use disp_functor_data_over_id_eq.
        - intros x xx ; cbn.
          apply (homotweqinvweq (Fo x)).
        - intros x y f xx yy ff ; cbn -[idtoiso_disp].
          etrans.
          {
            apply maponpaths_2.
            apply (FF_disp_functor_ff_inv H₂).
          }
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite !(assoc_disp_var (D := pr1 D₂)).
          rewrite !transport_f_f.
          etrans.
          {
            do 3 apply maponpaths.
            apply (idtoiso_disp_comp (D := pr1 D₂)).
          }
          rewrite pathsinv0l.
          unfold transportb.
          rewrite !mor_disp_transportf_prewhisker.
          rewrite transport_f_f.
          etrans.
          {
            do 2 apply maponpaths.
            apply id_right_disp.
          }
          unfold transportb.
          rewrite mor_disp_transportf_prewhisker.
          rewrite transport_f_f.
          apply maponpaths_2.
          apply homset_property.
      Qed.

      Proposition weq_and_ff_to_z_iso_disp_setcat_inv_right
        : disp_functor_composite_data F weq_and_ff_to_z_iso_disp_setcat_inv
          =
          pr1 (disp_functor_identity _).
      Proof.
        use disp_functor_data_over_id_eq.
        - intros x xx ; cbn.
          apply (homotinvweqweq (Fo x)).
        - intros x y f xx yy ff ; cbn -[idtoiso_disp].
          unfold transportb.
          refine (_ @ disp_functor_ff_FF_inv H₂ _).
          etrans.
          {
            apply maponpaths.
            exact (!(disp_functor_ff_FF_inv H₂ _)).
          }
          etrans.
          {
            refine (!_).
            apply (disp_functor_ff_inv_compose F H₂).
          }
          apply maponpaths.
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite transport_f_f.
          rewrite (disp_functor_transportf _ F).
          etrans.
          {
            do 2 apply maponpaths.
            apply (disp_functor_idtoiso_disp F).
          }
          unfold transportb.
          rewrite mor_disp_transportf_prewhisker.
          rewrite transport_f_f.
          rewrite (assoc_disp_var (D := pr1 D₂)).
          rewrite transport_f_f.
          etrans.
          {
            do 2 apply maponpaths.
            apply (idtoiso_disp_comp (D := pr1 D₂)).
          }
          unfold transportb.
          rewrite mor_disp_transportf_prewhisker.
          rewrite transport_f_f.
          etrans.
          {
            do 4 apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply (homotweqinvweqweq (Fo y)).
            }
            apply pathsinv0l.
          }
          etrans.
          {
            apply maponpaths.
            apply id_right_disp.
          }
          unfold transportb.
          rewrite transport_f_f.
          refine (!_).
          rewrite (disp_functor_comp F).
          unfold transportb.
          rewrite transport_f_f.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            apply (disp_functor_idtoiso_disp F).
          }
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite transport_f_f.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            do 2 apply maponpaths.
            apply (homotweqinvweqweq (Fo x)).
          }
          apply maponpaths_2.
          apply homset_property.
      Qed.
      
      Definition weq_and_ff_to_z_iso_disp_setcat
        : is_z_isomorphism (C := category_of_disp_setcat) F.
      Proof.
        use make_is_z_isomorphism.
        - exact weq_and_ff_to_z_iso_disp_setcat_inv.
        - split.
          + abstract
              (use disp_functor_eq ;
               exact weq_and_ff_to_z_iso_disp_setcat_inv_right).
          + abstract
              (use disp_functor_eq ;
               exact weq_and_ff_to_z_iso_disp_setcat_inv_left).
      Defined.
    End ToIso.

    Section FromIso.
      Context (H : is_z_isomorphism (C := category_of_disp_setcat) F).
      
      Let F' : disp_functor (functor_identity _) (pr1 D₂) (pr1 D₁)
        := pr1 H.
      
      Definition z_iso_to_obj_weq_disp_setcat
                 (x : C)
        : isweq (F x).
      Proof.
        use isweq_iso.
        - exact (λ xx, F' x xx).
        - abstract
            (intros xx ; cbn ;
             exact (disp_functor_eq_ob (pr12 H) xx)).
        - abstract
            (intros xx ; cbn ;
             exact (disp_functor_eq_ob (pr22 H) xx)).
      Defined.

      Definition z_iso_to_disp_functor_ff_disp_setcat
        : disp_functor_ff F.
      Proof.
        intros x y xx yy f.
        use isweq_iso.
        - intros ff.
          refine (transportf
                    (λ z, _ -->[ z ] _)
                    _
                    (idtoiso_disp (idpath _) _
                     ;; ♯ F' ff
                     ;; idtoiso_disp (idpath _) _)%mor_disp).
          + abstract
              (cbn ;
               rewrite id_left, id_right ;
               apply idpath).
          + exact (!(maponpaths (λ (FF : disp_functor _ _ _), FF x xx) (pr12 H))).
          + exact (maponpaths (λ (FF : disp_functor _ _ _), FF y yy) (pr12 H)).
        - intro ff ; cbn -[idtoiso_disp].
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            apply maponpaths.
            exact (!(disp_functor_eq_mor (!(pr12 H)) ff)).
          }
          rewrite mor_disp_transportf_prewhisker.
          rewrite mor_disp_transportf_postwhisker.
          rewrite !transport_f_f.
          cbn -[idtoiso_disp].
          rewrite !(assoc_disp_var (D := pr1 D₁)).
          rewrite !mor_disp_transportf_prewhisker.
          rewrite !transport_f_f.
          etrans.
          {
            do 4 apply maponpaths.
            apply (idtoiso_disp_comp (D := pr1 D₁)).
          }
          unfold transportb.
          rewrite !mor_disp_transportf_prewhisker.
          rewrite !transport_f_f.
          rewrite !assoc_disp.
          unfold transportb.
          rewrite !transport_f_f.
          etrans.
          {
            apply maponpaths.
            do 2 apply maponpaths_2.
            apply (idtoiso_disp_comp (D := pr1 D₁)).
          }
          unfold transportb.
          rewrite !mor_disp_transportf_postwhisker.
          rewrite !transport_f_f.
          etrans.
          {
            do 2 apply maponpaths.
            apply idtoiso_disp_disp_set_cat_refl.
          }
          etrans.
          {
            apply maponpaths.
            apply id_right_disp.
          }
          unfold transportb.
          rewrite !transport_f_f.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            apply idtoiso_disp_disp_set_cat_refl.
          }
          etrans.
          {
            apply maponpaths.
            apply id_left_disp.
          }
          unfold transportb.
          rewrite !transport_f_f.
          apply transportf_set.
          apply homset_property.
        - intro ff.
          cbn -[idtoiso_disp].
          rewrite (disp_functor_transportf _ F).
          rewrite (disp_functor_comp F).
          unfold transportb.
          rewrite transport_f_f.
          rewrite (disp_functor_comp F).
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite transport_f_f.
          etrans.
          {
            do 2 apply maponpaths.
            apply (disp_functor_idtoiso_disp F).
          }
          unfold transportb.
          rewrite mor_disp_transportf_prewhisker.
          rewrite transport_f_f.
          etrans.
          {
            apply maponpaths.
            do 2 apply maponpaths_2.
            apply (disp_functor_idtoiso_disp F).
          }
          unfold transportb.
          rewrite !mor_disp_transportf_postwhisker.
          rewrite transport_f_f.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            apply maponpaths.
            exact (!(disp_functor_eq_mor (!(pr22 H)) ff)).
          }
          rewrite mor_disp_transportf_prewhisker.
          rewrite mor_disp_transportf_postwhisker.
          rewrite !transport_f_f.
          cbn -[idtoiso_disp].
          rewrite !(assoc_disp_var (D := pr1 D₂)).
          rewrite !mor_disp_transportf_prewhisker.
          rewrite !transport_f_f.
          etrans.
          {
            do 4 apply maponpaths.
            apply (idtoiso_disp_comp (D := pr1 D₂)).
          }
          unfold transportb.
          rewrite !mor_disp_transportf_prewhisker.
          rewrite !transport_f_f.
          rewrite !(assoc_disp (D := pr1 D₂)).
          unfold transportb.
          rewrite !transport_f_f.
          etrans.
          {
            do 2 apply maponpaths.
            apply idtoiso_disp_disp_set_cat_refl.
          }
          etrans.
          {
            apply maponpaths.
            apply id_right_disp.
          }
          unfold transportb.
          rewrite !transport_f_f.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            apply (idtoiso_disp_comp (D := pr1 D₂)).
          }
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite !transport_f_f.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            apply idtoiso_disp_disp_set_cat_refl.
          }
          etrans.
          {
            apply maponpaths.
            apply id_left_disp.
          }
          unfold transportb.
          rewrite !transport_f_f.
          apply transportf_set.
          apply homset_property.
      Qed.
    End FromIso.
                 
    Definition is_z_isomorphism_disp_setcat_weq
      : (∏ (x : C), isweq (F x)) × disp_functor_ff F
        ≃
        is_z_isomorphism (C := category_of_disp_setcat) F.
    Proof.
      use weqimplimpl.
      - intros [ H₁ H₂ ].
        exact (weq_and_ff_to_z_iso_disp_setcat H₁ H₂).
      - intros H.
        split.
        + exact (z_iso_to_obj_weq_disp_setcat H).
        + exact (z_iso_to_disp_functor_ff_disp_setcat H).
      - use isapropdirprod.
        + use impred ; intro.
          apply isapropisweq.
        + apply isaprop_disp_functor_ff.
      - apply isaprop_is_z_isomorphism.
    Defined.
  End Isos.

  (** * 3. This category is univalent *)
  Proposition is_univalent_category_of_disp_setcat
    : is_univalent category_of_disp_setcat.
  Proof.
    intros D₁ D₂.
    use weqhomot.
    - refine (weqfibtototal _ _ _
              ∘ disp_cat_eq _ _
              ∘ path_sigma_hprop _ _ _ _)%weq.
      + use impred.
        intro.
        apply isapropisaset.
      + intro F.
        apply is_z_isomorphism_disp_setcat_weq.
    - intro p.
      induction p.
      use z_iso_eq.
      use disp_functor_eq.
      apply idpath.
  Qed.

  (** * 4. This displayed category of split cleavings *)
  Definition disp_cat_ob_mor_of_split_cleaving
    : disp_cat_ob_mor category_of_disp_setcat.
  Proof.
    simple refine (_ ,, _).
    - exact (λ D, ∑ (HD : cleaving (pr1 D)), is_split_id HD × is_split_comp HD).
    - exact (λ D₁ D₂ HD₁ HD₂ F, preserves_cleaving (pr1 HD₁) (pr1 HD₂) F).
  Defined.

  Proposition disp_cat_id_comp_of_split_cleaving
    : disp_cat_id_comp _ disp_cat_ob_mor_of_split_cleaving.
  Proof.
    split.
    - intros.
      apply identity_preserves_cleaving.
    - intros ? ? ? ? ? ? ? ? p₁ p₂.
      exact (composition_preserves_cleaving p₁ p₂).
  Qed.
  
  Definition disp_cat_data_of_split_cleaving
    : disp_cat_data category_of_disp_setcat.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_ob_mor_of_split_cleaving.
    - exact disp_cat_id_comp_of_split_cleaving.
  Defined.

  Proposition locally_propositional_disp_cat_of_split_cleaving
    : locally_propositional disp_cat_data_of_split_cleaving.
  Proof.
    intros D₁ D₂ F HF₁ HF₂.
    do 4 (use impred ; intro).
    use isaproptotal2.
    - intro.
      apply homsets_disp.
    - intros.
      apply D₂.
  Qed.
  
  Proposition disp_cat_axioms_of_split_cleaving
    : disp_cat_axioms _ disp_cat_data_of_split_cleaving.
  Proof.
    repeat split.
    - intros.
      apply locally_propositional_disp_cat_of_split_cleaving.
    - intros.
      apply locally_propositional_disp_cat_of_split_cleaving.
    - intros.
      apply locally_propositional_disp_cat_of_split_cleaving.
    - intros.
      apply isasetaprop.
      apply locally_propositional_disp_cat_of_split_cleaving.
  Qed.
    
  Definition disp_cat_of_split_cleaving
    : disp_cat category_of_disp_setcat.
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_data_of_split_cleaving.
    - exact disp_cat_axioms_of_split_cleaving.
  Defined.

  Proposition isaset_disp_ob_split_cleaving
              (D : category_of_disp_setcat)
    : isaset (disp_cat_of_split_cleaving D).
  Proof.
    use isaset_total2.
    - do 4 (use impred_isaset ; intro).
      use isaset_total2.
      + apply (pr2 D).
      + intro.
        apply isaset_total2.
        * apply homsets_disp.
        * intro.
          apply isasetaprop.
          apply isaprop_is_cartesian.
    - intro.
      apply isasetaprop.
      apply isapropdirprod.
      + do 2 (use impred ; intro).
        use isaproptotal2.
        * intro.
          apply homsets_disp.
        * intros.
          apply (pr2 D).
      + do 6 (use impred ; intro).
        use isaproptotal2.
        * intro.
          apply homsets_disp.
        * intros.
          apply (pr2 D).
  Qed.

  (** * 5. This displayed category is univalent *)
  Proposition is_univalent_disp_disp_cat_of_split_cleaving
    : is_univalent_disp disp_cat_of_split_cleaving.
  Proof.
    use is_univalent_disp_from_fibers.
    intros D HD₁ HD₂.
    use isweqimplimpl.
    - intros F.
      use subtypePath.
      {
        intro.
        apply isapropdirprod.
        + do 2 (use impred ; intro).
          use isaproptotal2.
          * intro.
            apply homsets_disp.
          * intros.
            apply (pr2 D).
        + do 6 (use impred ; intro).
          use isaproptotal2.
          * intro.
            apply homsets_disp.
          * intros.
            apply (pr2 D).
      }
      use funextsec ; intro x.
      use funextsec ; intro y.
      use funextsec ; intro f.
      use funextsec ; intro xx.
      induction F as [ HF HF' ] ; cbn in HF.
      clear HF'.
      specialize (HF y x f xx).
      induction HF as [ p q ].
      use total2_paths_f.
      + exact p.
      + use subtypePath.
        {
          intro.
          apply isaprop_is_cartesian.
        }
        rewrite pr1_transportf.
        cbn -[idtoiso_disp] in q.
        etrans.
        {
          apply maponpaths.
          exact (!(transportf_transpose_left (!q))).
        }
        rewrite transportf_precompose_disp.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite assoc_disp.
        unfold transportb.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (z_iso_disp_after_inv_mor (idtoiso_disp (idpath _) p)).
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite id_left_disp.
        unfold transportb.
        rewrite transport_f_f.
        apply transportf_set.
        apply homset_property.
    - apply isaset_disp_ob_split_cleaving.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply isaprop_preserves_cleaving.
        intro.
        apply (pr2 D).
  Qed.
  
  Definition category_of_split_disp_setcat
    : category
    := total_category disp_cat_of_split_cleaving.

  Proposition is_univalent_category_of_split_disp_setcat
    : is_univalent category_of_split_disp_setcat.
  Proof.
    use is_univalent_total_category.
    - exact is_univalent_category_of_disp_setcat.
    - exact is_univalent_disp_disp_cat_of_split_cleaving.
  Defined.

  Definition univalent_category_of_split_disp_setcat
    : univalent_category.
  Proof.
    use make_univalent_category.
    - exact category_of_split_disp_setcat.
    - exact is_univalent_category_of_split_disp_setcat.
  Defined.
End CatOfSplitDispSetCat.

(** * 6. Accessors *)
Definition split_disp_setcat
           (C : category)
  : UU
  := ob (category_of_split_disp_setcat C).

Definition make_split_disp_setcat
           {C : category}
           (D : disp_cat C)
           (HD : cleaving D)
           (H : is_split HD)
  : split_disp_setcat C
  := (D ,, pr22 H) ,, HD ,, pr1 H ,, pr12 H.
           
Coercion split_disp_setcat_to_disp_cat
         {C : category}
         (D : split_disp_setcat C)
  : disp_cat C
  := pr11 D.

Proposition isaset_split_disp_ob
            {C : category}
            (D : split_disp_setcat C)
            (x : C)
  : isaset (D x).
Proof.
  exact (pr21 D x).
Qed.

Coercion cleaving_of_split_disp_setcat
         {C : category}
         (D : split_disp_setcat C)
  : cleaving D
  := pr12 D.

Proposition is_split_split_disp_set_cat
            {C : category}
            (D : split_disp_setcat C)
  : is_split D.
Proof.
  repeat split.
  - exact (pr122 D).
  - exact (pr222 D).
  - exact (isaset_split_disp_ob D).
Qed.
            
Proposition isaset_disp_functor_split_disp_setcat
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
            (D₁ : disp_cat C₁)
            (D₂ : split_disp_setcat C₂)
  : isaset (disp_functor F D₁ D₂).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + do 2 (use impred_isaset ; intro).
      apply isaset_split_disp_ob.
    + intro.
      do 6 (use impred_isaset ; intro).
      apply homsets_disp.
  - intro.
    apply isasetaprop.
    apply isaprop_disp_functor_axioms.
Qed.

Proposition isaset_cartesian_disp_functor_split_disp_setcat
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
            (D₁ : disp_cat C₁)
            (D₂ : split_disp_setcat C₂)
  : isaset (cartesian_disp_functor F D₁ D₂).
Proof.
  use isaset_total2.
  - apply isaset_disp_functor_split_disp_setcat.
  - intro.
    apply isasetaprop.
    apply isaprop_is_cartesian_disp_functor.
Qed.

Proposition isaprop_preserves_cleaving
            {C₁ C₂ : category}
            {D₁ : disp_cat C₁}
            {D₂ : split_disp_setcat C₂}
            (I₁ : cleaving D₁)
            (I₂ : cleaving D₂)
            {F : C₁ ⟶ C₂}
            (FF : disp_functor F D₁ D₂)
  : isaprop (preserves_cleaving I₁ I₂ FF).
Proof.
  repeat (use impred ; intro).
  use isaproptotal2.
  - intro.
    apply homsets_disp.
  - intros.
    apply isaset_split_disp_ob.
Qed.

Definition split_disp_functor
           {C : category}
           (D₁ D₂ : split_disp_setcat C)
  : UU
  := D₁ --> D₂.

Definition make_split_disp_functor
           {C : category}
           {D₁ D₂ : split_disp_setcat C}
           (FF : disp_functor (functor_identity _) D₁ D₂)
           (H : preserves_cleaving D₁ D₂ FF)
  : split_disp_functor D₁ D₂
  := FF ,, H.

Proposition isaset_split_disp_functor
            {C : category}
            {D₁ D₂ : split_disp_setcat C}
  : isaset (split_disp_functor D₁ D₂).
Proof.
  use isaset_total2.
  - apply isaset_disp_functor_split_disp_setcat.
  - intro.
    apply isasetaprop.
    apply isaprop_preserves_cleaving.
Qed.

Coercion split_disp_functor_to_disp_functor
         {C : category}
         {D₁ D₂ : split_disp_setcat C}
         (FF : split_disp_functor D₁ D₂)
  : disp_functor (functor_identity _) D₁ D₂
  := pr1 FF.

Proposition split_disp_functor_preserves_cleaving
            {C : category}
            {D₁ D₂ : split_disp_setcat C}
            (FF : split_disp_functor D₁ D₂)
  : preserves_cleaving D₁ D₂ FF.
Proof.
  exact (pr2 FF).
Qed.

Proposition split_disp_functor_eq
            {C : category}
            {D₁ D₂ : split_disp_setcat C}
            {FF GG : split_disp_functor D₁ D₂}
            (p : pr11 FF = pr11 GG)
  : FF = GG.
Proof.
  use subtypePath.
  {
    intro ; simpl.
    apply isaprop_preserves_cleaving.
  }
  use disp_functor_eq.
  exact p.
Qed.
