(**

 The internal category of PERs

 One key result in realizability is that modest sets and partial equivalence relations
 are equivalent categories. The reason why this theorem is interesting, is because
 while modest sets form a class, partial equivalence relations form a set. This is because
 a modest set is a pair of a set with some additional structure.

 One application of this theorem is that we can construct an internal category of PERs
 in the category of assemblies. Since PERs form a set, we can make an assembly of PERs,
 and as morphisms we take all morphisms between the associated modest sets. We can interpret
 system F in the externalisation of this internal category. Note that this internal category
 can be constructed in the internal language of the realizability model as well.

 Content
 1. The assembly of objects
 2. The assembly of morphism
 3. The internal diagram
 4. Identity and composition
 5. The category laws
 6. The internal category of PERs and its externalisation

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import InternalCategories.InternalCat.
Require Import SplitFibration.SplitDispSetCat.
Require Import SplitFibration.Externalisation.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.BIAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.ModestSet.
Require Import Assemblies.PartialEqRel.
Require Import Assemblies.ModestSetEquiv.

Local Open Scope assembly.
Local Open Scope ca.
            
Section InternalCatOfPERs.
  Context (A : combinatory_algebra).

  (** * 1. The assembly of objects *)
  Definition per_internal_cat_ob
    : assembly A
    := discrete_assembly A (ca_per_hSet A).

  (** * 2. The assembly of morphism *)
  Definition dep_assembly_per_mor
    : dep_assembly
        (prod_assembly
           per_internal_cat_ob
           per_internal_cat_ob)
    := λ XY, function_assembly (per_to_assembly (pr1 XY)) (per_to_assembly (pr2 XY)).

  Definition per_internal_cat_mor
    : assembly A
    := total_assembly dep_assembly_per_mor.

  Definition make_per_internal_cat_mor
             (x y : per_internal_cat_ob)
             (f : assembly_morphism
                    (per_to_assembly x)
                    (per_to_assembly y))
    : per_internal_cat_mor
    := (x ,, y) ,, f.
             
  Definition per_internal_cat_mor_dom
             (f : per_internal_cat_mor)
    : per_internal_cat_ob
    := pr11 f.

  Definition per_internal_cat_mor_cod
             (f : per_internal_cat_mor)
    : per_internal_cat_ob
    := pr21 f.

  Definition per_internal_cat_mor_fun
             (f : per_internal_cat_mor)
    : assembly_morphism
        (per_to_assembly (per_internal_cat_mor_dom f))
        (per_to_assembly (per_internal_cat_mor_cod f))
    := pr2 f.
 
  Proposition per_internal_cat_mor_eq
              {f g : per_internal_cat_mor}
              (pd : per_internal_cat_mor_dom f = per_internal_cat_mor_dom g)
              (pc : per_internal_cat_mor_cod f = per_internal_cat_mor_cod g)
              (q : comp_assembly_morphism
                     (per_internal_cat_mor_fun f)
                     (per_to_assembly_on_eq pc)
                   =
                   comp_assembly_morphism
                     (per_to_assembly_on_eq pd)
                     (per_internal_cat_mor_fun g))
    : f = g.
  Proof.
    induction f as [ [ x₁ y₁ ] f ].
    induction g as [ [ x₂ y₂ ] g ].
    cbn in *.
    induction pd, pc.
    apply maponpaths.
    use assembly_morphism_eq.
    intro z.
    pose (q' := assembly_morphism_eq_point q z).
    refine (_ @ q' @ _).
    - rewrite per_to_assembly_on_eq_idpath.
      cbn.
      apply idpath.
    - rewrite per_to_assembly_on_eq_idpath.
      cbn.
      apply idpath.
  Qed.
              
  Definition per_internal_cat_dom
    : assembly_morphism
        per_internal_cat_mor
        per_internal_cat_ob
    := comp_assembly_morphism
         (total_assembly_pr _)
         (pr1_assembly_morphism _ _).

  Definition per_internal_cat_cod
    : assembly_morphism
        per_internal_cat_mor
        per_internal_cat_ob
    := comp_assembly_morphism
         (total_assembly_pr _)
         (pr2_assembly_morphism _ _).

  (** * 3. The internal diagram *)
  Definition per_internal_cat_diag
    : internal_cat_diag (cat_of_assembly A).
  Proof.
    use make_internal_cat_diag.
    - exact per_internal_cat_ob.
    - exact per_internal_cat_mor.
    - exact per_internal_cat_dom.
    - exact per_internal_cat_cod.
  Defined.

  (** * 4. Identity and composition *)
  Definition per_internal_cat_id
    : assembly_morphism
        per_internal_cat_ob
        per_internal_cat_mor.
  Proof.
    use make_assembly_morphism.
    - intro x.
      use make_per_internal_cat_mor.
      + exact x.
      + exact x.
      + exact (id_assembly_morphism _).
    - abstract
        (use hinhpr ;
         refine (K · (pair · I · I) ,, _) ;
         intros a R _ ;
         refine ((tt ,, tt) ,, _) ;
         intros b ;
         use setquotunivprop' ; [ intro ; apply propproperty | ] ;
         intros (c & p) q ;
         cbn in * ;
         rewrite combinatory_algebra_k_eq ;
         rewrite combinatory_algebra_pr2_pair ;
         rewrite combinatory_algebra_i_eq ;
         exact q).
  Defined.

  Definition per_internal_cat_comp_mor
             (fgp : pullback_assembly per_internal_cat_cod per_internal_cat_dom)
    : per_internal_cat_mor.
  Proof.
    use make_per_internal_cat_mor.
    - exact (per_internal_cat_mor_dom (pr1 fgp)).
    - exact (per_internal_cat_mor_cod (pr12 fgp)).
    - exact (comp_assembly_morphism
               (per_internal_cat_mor_fun (pr1 fgp))
               (comp_assembly_morphism
                  (per_to_assembly_on_eq (pr22 fgp))
                  (per_internal_cat_mor_fun (pr12 fgp)))).
  Defined.

  Arguments per_internal_cat_comp_mor /.

  Proposition per_internal_cat_comp_tracker
    : ∃ (a : A), tracks_morphism a per_internal_cat_comp_mor.
  Proof.
    use hinhpr.
    refine (internal_comp_combinator _ ,, _).
    intros a (f & g & pth) ((_ & p₁) & (_ & p₂)).
    refine ((tt ,, tt) ,, _).
    intro b.
    use setquotunivprop'.
    {
      intro.
      apply propproperty.
    }
    intros (c & q) r.
    induction f as [ [ R₁ R₂ ] f ].
    induction g as [ [ R₂' R₃ ] g ].
    cbn in pth.
    induction pth.
    cbn -[per_to_assembly_on_eq internal_comp_combinator].
    rewrite internal_comp_combinator_eq.
    rewrite combinatory_algebra_pr2_pair.
    rewrite internal_comp_combinator_help_eq.
    cbn in q, r.
    rewrite per_to_assembly_on_eq_idpath.
    cbn in p₁, p₂.
    specialize (p₁ b (setquotpr (dom_ca_per_quot_eqrel R₁) (c,, q)) r).
    cbn in p₁.
    specialize (p₂ _ (pr1 f (setquotpr (dom_ca_per_quot_eqrel R₁) (c,, q))) p₁).
    exact p₂.
  Qed.
  
  Definition per_internal_cat_comp
    : assembly_morphism
        (pullback_assembly per_internal_cat_cod per_internal_cat_dom)
        per_internal_cat_mor.
  Proof.
    use make_assembly_morphism.
    - exact per_internal_cat_comp_mor.
    - exact per_internal_cat_comp_tracker.
  Defined.
      
  Definition per_internal_cat_id_comp
    : internal_cat_id_comp
        (pullbacks_cat_of_assembly A)
        per_internal_cat_diag.
  Proof.
    split.
    - simple refine (_ ,, _ ,, _).
      + exact per_internal_cat_id.
      + abstract
          (use assembly_morphism_eq ;
           intros x ; cbn ;
           apply idpath).
      + abstract
          (use assembly_morphism_eq ;
           intros x ; cbn ;
           apply idpath).
    - simple refine (_ ,, _ ,, _).
      + exact per_internal_cat_comp.
      + abstract
          (use assembly_morphism_eq ;
           intros x ; cbn ;
           apply idpath).
      + abstract
          (use assembly_morphism_eq ;
           intros x ; cbn ;
           apply idpath).
  Defined.
  
  Definition per_internal_cat_data
    : internal_cat_data (pullbacks_cat_of_assembly A).
  Proof.
    use make_internal_cat_data.
    - exact per_internal_cat_diag.
    - exact per_internal_cat_id_comp.
  Defined.

  (** * 5. The category laws *)
  Proposition per_internal_cat_laws
    : disp_cat_axioms
        (cat_of_assembly A)
        (internal_cat_disp_cat_data per_internal_cat_data).
  Proof.
    use make_internal_cat_axioms.
    - intros Γ x y f.
      use internal_morphism_eq.
      use assembly_morphism_eq.
      intros γ.
      use per_internal_cat_mor_eq ; cbn.
      + exact (!(assembly_morphism_eq_point (internal_morphism_dom f) γ)).
      + apply idpath.
      + rewrite per_to_assembly_on_eq_idpath.
        use assembly_morphism_eq.
        intro q ; cbn -[per_to_assembly_on_eq].
        apply maponpaths.
        use per_to_assembly_on_eq_path.
        apply idpath.
    - intros Γ x y f.
      use internal_morphism_eq.
      use assembly_morphism_eq.
      intros γ.
      refine (!_).
      use per_internal_cat_mor_eq ; cbn.
      + apply idpath.
      + exact (assembly_morphism_eq_point (internal_morphism_cod f) γ).
      + rewrite per_to_assembly_on_eq_idpath.
        use assembly_morphism_eq.
        intro q ; cbn -[per_to_assembly_on_eq].
        use per_to_assembly_on_eq_path.
        apply idpath.
    - intros Γ w x y z f₁ f₂ f₃.
      use internal_morphism_eq.
      use assembly_morphism_eq.
      intros γ.
      cbn.
      apply maponpaths.
      use assembly_morphism_eq.
      intro q.
      cbn -[per_to_assembly_on_eq].
      apply maponpaths.
      use per_to_assembly_on_eq_path.
      apply maponpaths.
      use per_to_assembly_on_eq_path.
      apply idpath.
  Qed.

  (** * 6. The internal category of PERs and its externalisation *)
  Definition per_internal_cat
    : internal_cat (pullbacks_cat_of_assembly A).
  Proof.
    use make_internal_cat.
    - exact per_internal_cat_data.
    - exact per_internal_cat_laws.
  Defined.

  Definition per_split_fibration
    : split_disp_setcat (cat_of_assembly A)
    := externalisation_internal_cat _ per_internal_cat.
End InternalCatOfPERs.
