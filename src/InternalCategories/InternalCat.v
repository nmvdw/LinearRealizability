Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Local Open Scope cat.

(** * 1. Internal diagrams *)
Definition internal_cat_diag
           (C : category)
  : UU
  := ∑ (o a : C), a --> o × a --> o.

Definition make_internal_cat_diag
           {C : category}
           (o a : C)
           (src trg : a --> o)
  : internal_cat_diag C
  := o ,, a ,, src ,, trg.
           
Definition internal_cat_ob
           {C : category}
           (d : internal_cat_diag C)
  : C
  := pr1 d.

Definition internal_cat_mor
           {C : category}
           (d : internal_cat_diag C)
  : C
  := pr12 d.

Definition internal_cat_dom
           {C : category}
           (d : internal_cat_diag C)
  : internal_cat_mor d --> internal_cat_ob d
  := pr122 d.

Definition internal_cat_cod
           {C : category}
           (d : internal_cat_diag C)
  : internal_cat_mor d --> internal_cat_ob d
  := pr222 d.

(** * 2. Internal morphisms over morphisms *)
Definition internal_morphism_over
           {C : category}
           {d : internal_cat_diag C}
           {Γ Δ : C}
           (x : Γ --> internal_cat_ob d)
           (y : Δ --> internal_cat_ob d)
           (s : Γ --> Δ)
  : UU
  := ∑ (f : Γ --> internal_cat_mor d),
     (f · internal_cat_dom d = x)
     ×
     (f · internal_cat_cod d = s · y).

Proposition isaset_internal_morphism_over
            {C : category}
            {d : internal_cat_diag C}
            {Γ Δ : C}
            (x : Γ --> internal_cat_ob d)
            (y : Δ --> internal_cat_ob d)
            (s : Γ --> Δ)
  : isaset (internal_morphism_over x y s).
Proof.
  use isaset_total2.
  - apply homset_property.
  - intro.
    apply isasetaprop.
    apply isapropdirprod ; apply homset_property.
Qed.

Definition make_internal_morphism_over
           {C : category}
           {d : internal_cat_diag C}
           {Γ Δ : C}
           {x : Γ --> internal_cat_ob d}
           {y : Δ --> internal_cat_ob d}
           {s : Γ --> Δ}
           (f : Γ --> internal_cat_mor d)
           (p : f · internal_cat_dom d = x)
           (q : f · internal_cat_cod d = s · y)
  : internal_morphism_over x y s
  := f ,, p ,, q.
           
Coercion internal_morphism_over_to_mor
         {C : category}
         {d : internal_cat_diag C}
         {Γ Δ : C}
         {x : Γ --> internal_cat_ob d}
         {y : Δ --> internal_cat_ob d}
         {s : Γ --> Δ}
         (f : internal_morphism_over x y s)
  : Γ --> internal_cat_mor d
  := pr1 f.

Definition internal_morphism_over_dom
           {C : category}
           {d : internal_cat_diag C}
           {Γ Δ : C}
           {x : Γ --> internal_cat_ob d}
           {y : Δ --> internal_cat_ob d}
           {s : Γ --> Δ}
           (f : internal_morphism_over x y s)
  : f · internal_cat_dom d = x
  := pr12 f.

Definition internal_morphism_over_cod
           {C : category}
           {d : internal_cat_diag C}
           {Γ Δ : C}
           {x : Γ --> internal_cat_ob d}
           {y : Δ --> internal_cat_ob d}
           {s : Γ --> Δ}
           (f : internal_morphism_over x y s)
  : f · internal_cat_cod d = s · y
  := pr22 f.

Proposition internal_morphism_over_eq
            {C : category}
            {d : internal_cat_diag C}
            {Γ Δ : C}
            {x : Γ --> internal_cat_ob d}
            {y : Δ --> internal_cat_ob d}
            {s : Γ --> Δ}
            {f g : internal_morphism_over x y s}
            (p : internal_morphism_over_to_mor f = g)
  : f = g.
Proof.
  use subtypePath.
  {
    intro.
    apply isapropdirprod ; apply homset_property.
  }
  exact p.
Qed.

Definition internal_morphism_over_precomp
           {C : category}
           {d : internal_cat_diag C}
           {Γ₁ Γ₂ Γ₃ : C}
           {x : Γ₂ --> internal_cat_ob d}
           {y : Γ₃ --> internal_cat_ob d}
           {s : Γ₂ --> Γ₃}
           (f : internal_morphism_over x y s)
           (s' : Γ₁ --> Γ₂)
  : internal_morphism_over (s' · x) y (s' · s).
Proof.
  use make_internal_morphism_over.
  - exact (s' · f).
  - abstract
      (rewrite !assoc' ;
       apply maponpaths ;
       apply internal_morphism_over_dom).
  - abstract
      (rewrite !assoc' ;
       apply maponpaths ;
       apply internal_morphism_over_cod).
Defined.

(** * 2. Internal morphisms over the identity *)
Definition internal_morphism
           {C : category}
           {d : internal_cat_diag C}
           {Γ : C}
           (x y : Γ --> internal_cat_ob d)
  : UU
  := internal_morphism_over x y (identity _).

Proposition isaset_internal_morphism
            {C : category}
            {d : internal_cat_diag C}
            {Γ : C}
            (x y : Γ --> internal_cat_ob d)
  : isaset (internal_morphism x y).
Proof.
  apply isaset_internal_morphism_over.
Qed.

Definition make_internal_morphism
           {C : category}
           {d : internal_cat_diag C}
           {Γ : C}
           {x y : Γ --> internal_cat_ob d}
           (f : Γ --> internal_cat_mor d)
           (p : f · internal_cat_dom d = x)
           (q : f · internal_cat_cod d = y)
  : internal_morphism x y.
Proof.
  use make_internal_morphism_over.
  - exact f.
  - exact p.
  - abstract
      (rewrite id_left ;
       exact q).
Defined.
           
Coercion internal_morphism_to_mor
         {C : category}
         {d : internal_cat_diag C}
         {Γ : C}
         {x y : Γ --> internal_cat_ob d}
         (f : internal_morphism x y)
  : Γ --> internal_cat_mor d
  := pr1 f.

Definition internal_morphism_dom
           {C : category}
           {d : internal_cat_diag C}
           {Γ : C}
           {x y : Γ --> internal_cat_ob d}
           (f : internal_morphism x y)
  : f · internal_cat_dom d = x
  := internal_morphism_over_dom f.

Definition internal_morphism_cod
           {C : category}
           {d : internal_cat_diag C}
           {Γ : C}
           {x y : Γ --> internal_cat_ob d}
           (f : internal_morphism x y)
  : f · internal_cat_cod d = y.
Proof.
  refine (internal_morphism_over_cod f @ _).
  apply id_left.
Qed.

Proposition internal_morphism_eq
            {C : category}
            {d : internal_cat_diag C}
            {Γ : C}
            {x y : Γ --> internal_cat_ob d}
            {f g : internal_morphism x y}
            (p : internal_morphism_to_mor f = g)
  : f = g.
Proof.
  use internal_morphism_over_eq.
  exact p.
Qed.

Definition internal_morphism_over_to_internal_morphism
           {C : category}
           {d : internal_cat_diag C}
           {Γ Δ : C}
           {x : Γ --> internal_cat_ob d}
           {y : Δ --> internal_cat_ob d}
           {s : Γ --> Δ}
           (f : internal_morphism_over x y s)
  : internal_morphism x (s · y).
Proof.
  use make_internal_morphism.
  - exact f.
  - abstract
      (apply internal_morphism_over_dom).
  - abstract
      (apply internal_morphism_over_cod).
Defined.
           
(** * 3. The data of the externalisation *)
Definition internal_cat_disp_cat_ob_mor
           {C : category}
           (d : internal_cat_diag C)
  : disp_cat_ob_mor C.
Proof.
  simple refine (_ ,, _).
  - exact (λ Γ, Γ --> internal_cat_ob d).
  - exact (λ Γ Δ x y s, internal_morphism_over x y s).
Defined.

Definition internal_cat_id_comp
           {C : category}
           (PB : Pullbacks C)
           (d : internal_cat_diag C)
  : UU
  := (∑ (i : internal_cat_ob d --> internal_cat_mor d),
      (i · internal_cat_dom d = identity _)
      ×
      (i · internal_cat_cod d = identity _))
     ×
     (∑ (c : PB _ _ _ (internal_cat_cod d) (internal_cat_dom d) --> internal_cat_mor d),
      (c · internal_cat_dom d = PullbackPr1 _ · internal_cat_dom d)
      ×
      (c · internal_cat_cod d = PullbackPr2 _ · internal_cat_cod d)).

Definition internal_cat_data
           {C : category}
           (PB : Pullbacks C)
  : UU
  := ∑ (d : internal_cat_diag C), internal_cat_id_comp PB d.

Definition make_internal_cat_data
           {C : category}
           (PB : Pullbacks C)
           (d : internal_cat_diag C)
           (ic : internal_cat_id_comp PB d)
  : internal_cat_data PB
  := d ,, ic.

Coercion internal_cat_data_to_diag
         {C : category}
         {PB : Pullbacks C}
         (d : internal_cat_data PB)
  : internal_cat_diag C
  := pr1 d.

Definition internal_cat_id
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat_data PB)
  : internal_cat_ob d --> internal_cat_mor d
  := pr112 d.

Definition internal_cat_id_dom
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat_data PB)
  : internal_cat_id d · internal_cat_dom d = identity _
  := pr1 (pr212 d).

Definition internal_cat_id_cod
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat_data PB)
  : internal_cat_id d · internal_cat_cod d = identity _
  := pr2 (pr212 d).

Definition internal_cat_comp
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat_data PB)
  : PB _ _ _ (internal_cat_cod d) (internal_cat_dom d) --> internal_cat_mor d
  := pr122 d.

Definition internal_cat_comp_dom
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat_data PB)
  : internal_cat_comp d · internal_cat_dom d = PullbackPr1 _ · internal_cat_dom d
  := pr1 (pr222 d).

Definition internal_cat_comp_cod
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat_data PB)
  : internal_cat_comp d · internal_cat_cod d = PullbackPr2 _ · internal_cat_cod d
  := pr2 (pr222 d).

Definition internal_cat_id_mor
           {C : category}
           {PB : Pullbacks C}
           {d : internal_cat_data PB}
           {Γ : C}
           (x : Γ --> internal_cat_ob d)
  : internal_morphism x x.
Proof.
  use make_internal_morphism.
  - exact (x · internal_cat_id d).
  - abstract
      (rewrite !assoc' ;
       rewrite internal_cat_id_dom ;
       apply id_right).
  - abstract
      (rewrite !assoc' ;
       rewrite internal_cat_id_cod ;
       apply id_right).
Defined.

Notation "'idi'" := internal_cat_id_mor : cat.

Definition internal_cat_comp_mor_over
           {C : category}
           {PB : Pullbacks C}
           {d : internal_cat_data PB}
           {Γ₁ Γ₂ Γ₃ : C}
           {x₁ : Γ₁ --> internal_cat_ob d}
           {x₂ : Γ₂ --> internal_cat_ob d}
           {x₃ : Γ₃ --> internal_cat_ob d}
           {s₁ : Γ₁ --> Γ₂}
           {s₂ : Γ₂ --> Γ₃}
           (f₁ : internal_morphism_over x₁ x₂ s₁)
           (f₂ : internal_morphism_over x₂ x₃ s₂)
  : internal_morphism_over x₁ x₃ (s₁ · s₂).
Proof.
  use make_internal_morphism_over.
  - refine (PullbackArrow _ _ f₁ (s₁ · f₂) _ · internal_cat_comp d).
    abstract
      (rewrite assoc' ;
       rewrite internal_morphism_over_dom, internal_morphism_over_cod ;
       apply idpath).
  - abstract
      (rewrite assoc' ;
       rewrite internal_cat_comp_dom ;
       rewrite assoc ;
       rewrite PullbackArrow_PullbackPr1 ;
       rewrite internal_morphism_over_dom ;
       apply idpath).
  - abstract
      (rewrite assoc' ;
       rewrite internal_cat_comp_cod ;
       rewrite assoc ;
       rewrite PullbackArrow_PullbackPr2 ;
       rewrite !assoc' ;
       rewrite internal_morphism_over_cod ;
       apply idpath).
Defined.

Definition internal_cat_comp_mor
           {C : category}
           {PB : Pullbacks C}
           {d : internal_cat_data PB}
           {Γ : C}
           {x₁ x₂ x₃ : Γ --> internal_cat_ob d}
           (f₁ : internal_morphism x₁ x₂)
           (f₂ : internal_morphism x₂ x₃)
  : internal_morphism x₁ x₃.
Proof.
  use make_internal_morphism.
  - refine (PullbackArrow _ _ f₁ f₂ _ · internal_cat_comp d).
    abstract
      (rewrite internal_morphism_dom, internal_morphism_cod ;
       apply idpath).
  - abstract
      (rewrite assoc' ;
       rewrite internal_cat_comp_dom ;
       rewrite assoc ;
       rewrite PullbackArrow_PullbackPr1 ;
       rewrite internal_morphism_dom ;
       apply idpath).
  - abstract
      (rewrite assoc' ;
       rewrite internal_cat_comp_cod ;
       rewrite assoc ;
       rewrite PullbackArrow_PullbackPr2 ;
       rewrite internal_morphism_cod ;
       apply idpath).
Defined.

Notation "f₁ ·i f₂" := (internal_cat_comp_mor f₁ f₂) (at level 40, left associativity) : cat.

Definition internal_cat_disp_cat_id_comp
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat_data PB)
  : disp_cat_id_comp _ (internal_cat_disp_cat_ob_mor d).
Proof.
  split ; cbn.
  - exact (λ Γ x, idi x).
  - exact (λ Γ₁ Γ₂ Γ₃ s₁ s₂ x y z f g, internal_cat_comp_mor_over f g).
Defined.

Definition internal_cat_disp_cat_data
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat_data PB)
  : disp_cat_data C.
Proof.
  simple refine (_ ,, _).
  - exact (internal_cat_disp_cat_ob_mor d).
  - exact (internal_cat_disp_cat_id_comp d).
Defined.

(** * 4. Internal categories *)
Definition internal_cat
           {C : category}
           (PB : Pullbacks C)
  : UU
  := ∑ (d : internal_cat_data PB),
     disp_cat_axioms C (internal_cat_disp_cat_data d).

Definition make_internal_cat
           {C : category}
           (PB : Pullbacks C)
           (d : internal_cat_data PB)
           (H : disp_cat_axioms C (internal_cat_disp_cat_data d))
  : internal_cat PB
  := d ,, H.

Coercion internal_cat_to_data
         {C : category}
         {PB : Pullbacks C}
         (d : internal_cat PB)
  : internal_cat_data PB
  := pr1 d.

Definition internal_cat_composable
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat PB)
  : C
  := PB _ _ _ (internal_cat_cod d) (internal_cat_dom d).

Definition internal_cat_composable_left
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat PB)
  : internal_cat_composable d --> internal_cat_mor d
  := PullbackPr1 _.

Definition internal_cat_composable_right
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat PB)
  : internal_cat_composable d --> internal_cat_mor d
  := PullbackPr2 _.

Proposition internal_cat_composable_cod_dom
            {C : category}
            {PB : Pullbacks C}
            (d : internal_cat PB)
  : internal_cat_composable_left d · internal_cat_cod d
    =
    internal_cat_composable_right d · internal_cat_dom d.
Proof.
  apply PullbackSqrCommutes.
Qed.

Definition internal_cat_composable_left_mor
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat PB)
  : internal_morphism
      (internal_cat_composable_left d · internal_cat_dom d)
      (internal_cat_composable_left d · internal_cat_cod d).
Proof.
  use make_internal_morphism.
  - exact (internal_cat_composable_left d).
  - apply idpath.
  - apply idpath.
Defined.

Definition internal_cat_composable_right_mor
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat PB)
  : internal_morphism
      (internal_cat_composable_left d · internal_cat_cod d)
      (internal_cat_composable_right d · internal_cat_cod d).
Proof.
  use make_internal_morphism.
  - exact (internal_cat_composable_right d).
  - abstract
      (rewrite internal_cat_composable_cod_dom ;
       apply idpath).
  - apply idpath.
Defined.

Definition is_internal_preorder
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat PB)
  : UU
  := ∏ (Γ : C)
       (x y : Γ --> internal_cat_ob d)
       (f g : internal_morphism x y),
     f = g.

Definition internal_preorder
           {C : category}
           (PB : Pullbacks C)
  : UU
  := ∑ (d : internal_cat PB), is_internal_preorder d.

Coercion internal_preorder_to_internal_cat
         {C : category}
         {PB : Pullbacks C}
         (d : internal_preorder PB)
  : internal_cat PB
  := pr1 d.

Proposition internal_preorder_morphism_eq
            {C : category}
            {PB : Pullbacks C}
            {d : internal_preorder PB}
            {Γ : C}
            {x y : Γ --> internal_cat_ob d}
            (f g : internal_morphism x y)
  : f = g.
Proof.
  apply (pr2 d).
Qed.
            
(** * 5. The externalisation *)
Definition internal_cat_disp_cat
           {C : category}
           {PB : Pullbacks C}
           (d : internal_cat PB)
  : disp_cat C.
Proof.
  simple refine (_ ,, _).
  - exact (internal_cat_disp_cat_data d).
  - exact (pr2 d).
Defined.

Proposition locally_propositionalinternal_preorder_disp_cat
            {C : category}
            {PB : Pullbacks C}
            (d : internal_preorder PB)
  : locally_propositional (internal_cat_disp_cat d).
Proof.
  intros Γ₁ Γ₂ s x y.
  use invproofirrelevance.
  intros f g.
  pose (f' := internal_morphism_over_to_internal_morphism f).
  pose (g' := internal_morphism_over_to_internal_morphism g).
  pose (internal_preorder_morphism_eq f' g').
  use internal_morphism_over_eq.
  exact (maponpaths pr1 p).
Qed.

Proposition locally_propositional_to_is_internal_preorder
            {C : category}
            {PB : Pullbacks C}
            (d : internal_cat PB)
            (H : locally_propositional (internal_cat_disp_cat d))
  : is_internal_preorder d.
Proof.
  intros Γ x y f g.
  apply (H Γ Γ (identity _) x y f g).
Qed.

Proposition transportf_internal_morphism_dom_eq
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat_data PB}
            {Γ Δ : C}
            (y : Δ --> internal_cat_ob d)
            {x₁ x₂ : Γ --> internal_cat_ob d}
            (s : Γ --> Δ)
            (p : x₁ = x₂)
            (f : internal_morphism_over x₁ y s)
  : internal_morphism_over_to_mor (transportf (λ x, internal_morphism_over x y s) p f)
    =
    f.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition transportf_internal_morphism_cod_eq
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat_data PB}
            {Γ Δ : C}
            {y₁ y₂ : Δ --> internal_cat_ob d}
            (x : Γ --> internal_cat_ob d)
            (s : Γ --> Δ)
            (p : y₁ = y₂)
            (f : internal_morphism_over x y₁ s)
  : internal_morphism_over_to_mor (transportf (λ y, internal_morphism_over x y s) p f)
    =
    f.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition transportf_internal_morphism_mor_eq
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat_data PB}
            {Γ Δ : C}
            (y : Δ --> internal_cat_ob d)
            (x : Γ --> internal_cat_ob d)
            {s₁ s₂ : Γ --> Δ}
            (p : s₁ = s₂)
            (f : internal_morphism_over x y s₁)
  : internal_morphism_over_to_mor (transportf (λ s, internal_morphism_over x y s) p f)
    =
    f.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition internal_morphism_id_left
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x y : Γ --> internal_cat_ob d}
            (f : internal_morphism x y)
  : idi x ·i f = f.
Proof.
  use internal_morphism_eq.
  pose proof (maponpaths pr1 (id_left_disp (D := internal_cat_disp_cat d) f)
               @ transportf_internal_morphism_mor_eq _ _ _ _)
    as path.
  refine (_ @ path).
  cbn.
  apply maponpaths_2.
  use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
  - rewrite PullbackArrow_PullbackPr1.
    apply idpath.
  - rewrite PullbackArrow_PullbackPr2.
    rewrite id_left.
    apply idpath.
Qed.

Proposition internal_morphism_id_right
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x y : Γ --> internal_cat_ob d}
            (f : internal_morphism x y)
  : f ·i idi y = f.
Proof.
  use internal_morphism_eq.
  pose proof (maponpaths pr1 (id_right_disp (D := internal_cat_disp_cat d) f)
               @ transportf_internal_morphism_mor_eq _ _ _ _)
    as path.
  refine (_ @ path).
  cbn.
  apply maponpaths_2.
  use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
  + rewrite PullbackArrow_PullbackPr1.
    apply idpath.
  + rewrite PullbackArrow_PullbackPr2.
    rewrite id_left.
    apply idpath.
Qed.

Proposition internal_morphism_assoc
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x₁ x₂ x₃ x₄ : Γ --> internal_cat_ob d}
            (f₁ : internal_morphism x₁ x₂)
            (f₂ : internal_morphism x₂ x₃)
            (f₃ : internal_morphism x₃ x₄)
  : f₁ ·i (f₂ ·i f₃) = (f₁ ·i f₂) ·i f₃.
Proof.
  use internal_morphism_eq.
  pose proof (maponpaths pr1 (assoc_disp (D := internal_cat_disp_cat d) f₁ f₂ f₃)
              @ transportf_internal_morphism_mor_eq _ _ _ _)
    as path.
  cbn in path.
  refine (_ @ path @ _) ; clear path ; cbn.
  - apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      rewrite id_left.
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      * rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      * rewrite PullbackArrow_PullbackPr2.
        rewrite id_left.
        apply idpath.
  - apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      * rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      * rewrite PullbackArrow_PullbackPr2.
        rewrite id_left.
        apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      rewrite !id_left.
      apply idpath.
Qed.

Proposition internal_morphism_assoc'
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x₁ x₂ x₃ x₄ : Γ --> internal_cat_ob d}
            (f₁ : internal_morphism x₁ x₂)
            (f₂ : internal_morphism x₂ x₃)
            (f₃ : internal_morphism x₃ x₄)
  : (f₁ ·i f₂) ·i f₃ = (f₁ ·i (f₂ ·i f₃)).
Proof.
  refine (!_).
  apply internal_morphism_assoc.
Qed.

Definition make_internal_cat_axioms
           {C : category}
           (PB : Pullbacks C)
           (d : internal_cat_data PB)
           (idl : ∏ (Γ : C)
                    (x y : Γ --> internal_cat_ob d)
                    (f : internal_morphism x y),
                  idi x ·i f = f)
           (idr : ∏ (Γ : C)
                    (x y : Γ --> internal_cat_ob d)
                    (f : internal_morphism x y),
                  f ·i idi y = f)
           (asc : ∏ (Γ : C)
                    (x₁ x₂ x₃ x₄ : Γ --> internal_cat_ob d)
                    (f₁ : internal_morphism x₁ x₂)
                    (f₂ : internal_morphism x₂ x₃)
                    (f₃ : internal_morphism x₃ x₄),
                  f₁ ·i (f₂ ·i f₃) = (f₁ ·i f₂) ·i f₃)
  : disp_cat_axioms C (internal_cat_disp_cat_data d).
Proof.
  repeat split.
  - intros Γ Δ s x y f.
    use internal_morphism_over_eq.
    specialize (idl _ _ _ (internal_morphism_over_to_internal_morphism f)).
    refine (_ @ maponpaths pr1 idl @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
    cbn.
    apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      apply id_left.
  - intros Γ Δ s x y f.
    use internal_morphism_over_eq.
    specialize (idr _ _ _ (internal_morphism_over_to_internal_morphism f)).
    refine (_ @ maponpaths pr1 idr @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
    cbn.
    apply maponpaths_2.
    use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
    + rewrite PullbackArrow_PullbackPr1.
      apply idpath.
    + rewrite PullbackArrow_PullbackPr2.
      apply assoc.
  - intros Γ₁ Γ₂ Γ₃ Γ₄ s₁ s₂ s₃ w x y z f₁ f₂ f₃.
    use internal_morphism_over_eq.
    specialize (asc
                  _ _ _ _ _
                  (internal_morphism_over_to_internal_morphism f₁)
                  (internal_morphism_over_to_internal_morphism
                     (internal_morphism_over_precomp f₂ _))
                  (internal_morphism_over_to_internal_morphism
                     (internal_morphism_over_precomp f₃ _))).
    refine (_ @ maponpaths pr1 asc @ _ @ !(transportf_internal_morphism_mor_eq _ _ _ _)).
    + cbn.
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      * rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      * rewrite PullbackArrow_PullbackPr2.
        rewrite !assoc.
        apply maponpaths_2.
        use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
        ** rewrite !assoc'.
           rewrite PullbackArrow_PullbackPr1.
           apply idpath.
        ** rewrite !assoc'.
           rewrite PullbackArrow_PullbackPr2.
           apply idpath.
    + cbn.
      apply maponpaths_2.
      use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
      * rewrite PullbackArrow_PullbackPr1.
        apply maponpaths_2.
        use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
        ** rewrite PullbackArrow_PullbackPr1.
           apply idpath.
        ** rewrite PullbackArrow_PullbackPr2.
           apply idpath.
      * rewrite PullbackArrow_PullbackPr2.
        apply idpath.
  - intros ; cbn.
    apply isaset_internal_morphism_over.
Qed.

(** * 6. The externalisation is a fibration *)
Proposition internal_morphism_id_right_pb
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ Δ : C}
            {y : Δ --> internal_cat_ob d}
            {x : Γ --> internal_cat_ob d}
            {s : Γ --> Δ}
            (f : internal_morphism_over x y s)
            {g₁ g₂ : Γ --> internal_cat_mor d}
            (p : pr1 f = g₁)
            (q : s · (y · internal_cat_id d) = g₂)
            (r : g₁ · internal_cat_cod d = g₂ · internal_cat_dom d)
  : PullbackArrow _ _ g₁ g₂ r · internal_cat_comp d = f.
Proof.  
  pose proof (maponpaths pr1 (id_right_disp (D := internal_cat_disp_cat d) f)
               @ transportf_internal_morphism_mor_eq _ _ _ _)
    as path.
  cbn in path.
  refine (_ @ path).
  cbn.
  induction p, q.
  apply maponpaths_2.
  apply maponpaths.
  apply homset_property.
Qed.

Section InternalCatCleaving.
  Context {C : category}
          {PB : Pullbacks C}
          (d : internal_cat PB).

  Section Lift.
    Context {Γ Δ : C}
            (s : Δ --> Γ)
            (x : Γ --> internal_cat_ob d).

    Definition internal_cat_lift
      : Δ --> internal_cat_ob d
      := s · x.

    Definition internal_cat_lift_mor
      : internal_morphism_over internal_cat_lift x s.
    Proof.
      use make_internal_morphism_over.
      - exact (s · x · internal_cat_id d).
      - abstract
          (rewrite !assoc' ;
           rewrite internal_cat_id_dom ;
           rewrite id_right ;
           apply idpath).
      - abstract
          (rewrite !assoc' ;
           rewrite internal_cat_id_cod ;
           rewrite id_right ;
           apply idpath).
    Defined.

    Context {Γ' : C}
            {s' : Γ' --> Δ}
            {y : Γ' --> internal_cat_ob d}
            (f : internal_morphism_over y x (s' · s)).

    Definition internal_cat_factorisation
      : internal_morphism_over y internal_cat_lift s'.
    Proof.
      use make_internal_morphism_over.
      - exact f.
      - abstract
          (rewrite internal_morphism_over_dom ;
           apply idpath).
      - abstract
          (rewrite internal_morphism_over_cod ;
           rewrite !assoc' ;
           apply idpath).
    Defined.
  End Lift.
  
  Definition internal_cat_to_cleaving         
    : cleaving (internal_cat_disp_cat d).
  Proof.
    intros Γ Δ s x.
    simple refine (_ ,, _).
    - exact (internal_cat_lift s x).
    - simple refine (_ ,, _).
      + exact (internal_cat_lift_mor s x).
      + intros Γ' s' y f.
        use iscontraprop1.
        * abstract
            (use invproofirrelevance ;
             intros ζ₁ ζ₂ ;
             use subtypePath ; [ intro ; apply homsets_disp | ] ;
             use internal_morphism_over_eq ;
             pose proof (maponpaths (λ z, pr1 z) (pr2 ζ₁ @ !(pr2 ζ₂))) as p ;
             cbn -[internal_cat_comp_mor] in p ;
             refine (!_ @ p @ _) ;
             (apply internal_morphism_id_right_pb ; [ apply idpath | ]) ;
             unfold internal_cat_lift, internal_cat_lift_mor ; cbn ;
             rewrite !assoc' ;
             apply idpath).
        * simple refine (_ ,, _).
          ** exact (internal_cat_factorisation s x f).
          ** abstract
              (use internal_morphism_over_eq ;
               use internal_morphism_id_right_pb ; [ apply idpath | ] ;
               unfold internal_cat_lift_mor ; cbn ;
               rewrite !assoc' ;
               apply idpath).
  Defined.

  Proposition is_split_internal_cat_to_cleaving
    : is_split internal_cat_to_cleaving.
  Proof.
    repeat split.
    - intros Γ x.
      simple refine (_ ,, _).
      + apply id_left.
      + use internal_morphism_over_eq ; cbn.
        unfold transportb.
        rewrite transportf_internal_morphism_dom_eq ; cbn.
        rewrite id_left.
        apply idpath.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ x.
      simple refine (_ ,, _).
      + apply assoc'.
      + use internal_morphism_over_eq.
        refine (!_).
        refine (transportf_internal_morphism_dom_eq _ _ _ _ @ _).
        use internal_morphism_id_right_pb ; cbn.
        * unfold internal_cat_lift.
          rewrite !assoc'.
          apply idpath.
        * unfold internal_cat_lift.
          rewrite !assoc'.
          apply idpath.
    - intro.
      apply homset_property.
  Qed.
End InternalCatCleaving.

(** * 7. Equalities to morphisms *)
Definition eq_to_internal_morphism
           {C : category}
           {PB : Pullbacks C}
           {d : internal_cat_data PB}
           {Γ : C}
           {x y : Γ --> internal_cat_ob d}
           (p : x = y)
  : internal_morphism x y.
Proof.
  use make_internal_morphism.
  - exact (x · internal_cat_id d).
  - abstract
      (induction p ;
       rewrite !assoc' ;
       rewrite internal_cat_id_dom ;
       apply id_right).
  - abstract
      (induction p ;
       rewrite !assoc' ;
       rewrite internal_cat_id_cod ;
       apply id_right).
Defined.

Proposition eq_to_internal_morphism_id
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat_data PB}
            {Γ : C}
            (x : Γ --> internal_cat_ob d)
            (p : x = x)
  : eq_to_internal_morphism p = idi _.
Proof.
  assert (p = idpath _) as -> by apply homset_property.
  use internal_morphism_eq ; cbn.
  apply idpath.
Qed.

Proposition eq_to_internal_morphism_comp
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x y z : Γ --> internal_cat_ob d}
            (p : x = y)
            (q : y = z)
  : eq_to_internal_morphism (p @ q)
    =
    eq_to_internal_morphism p ·i eq_to_internal_morphism q.
Proof.
  induction p, q ; cbn.
  rewrite !eq_to_internal_morphism_id.
  rewrite internal_morphism_id_left.
  apply idpath.
Qed.

Proposition eq_to_internal_morphism_inv
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x y : Γ --> internal_cat_ob d}
            (p : x = y)
            (q : y = x)
  : eq_to_internal_morphism q ·i eq_to_internal_morphism p
    =
    idi _.
Proof.
  assert (q = !p) as -> by apply homset_property.
  induction p ; cbn.
  rewrite !eq_to_internal_morphism_id.
  rewrite internal_morphism_id_left.
  apply idpath.
Qed.

Proposition eq_to_internal_morphism_left
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x y z : Γ --> internal_cat_ob d}
            (p : x = y)
            (f : internal_morphism y z)
  : internal_morphism_to_mor (eq_to_internal_morphism p ·i f) = f.
Proof.
  refine (_ @ maponpaths pr1 (internal_morphism_id_left f)).
  cbn.
  apply maponpaths_2.
  induction p.
  use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
  - rewrite PullbackArrow_PullbackPr1.
    apply idpath.
  - rewrite PullbackArrow_PullbackPr2.
    apply idpath.
Qed.

Proposition eq_to_internal_morphism_left_over
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ₁ Γ₂ : C}
            {x y : Γ₁ --> internal_cat_ob d}
            {z : Γ₂ --> internal_cat_ob d}
            {s : Γ₁ --> Γ₂}
            (p : x = y)
            (f : internal_morphism_over y z s)
  : internal_morphism_over_to_mor
      (internal_cat_comp_mor_over
         (eq_to_internal_morphism p)
         f)
    =
    f.
Proof.
  pose (f' := internal_morphism_over_to_internal_morphism f).
  refine (_ @ maponpaths pr1 (internal_morphism_id_left f')).
  induction p ; cbn.
  apply maponpaths_2.
  use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
  - rewrite PullbackArrow_PullbackPr1.
    apply idpath.
  - rewrite PullbackArrow_PullbackPr2.
    apply id_left.
Qed.

Proposition eq_to_internal_morphism_right_over
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ₁ Γ₂ : C}
            {x : Γ₁ --> internal_cat_ob d}
            {y z : Γ₂ --> internal_cat_ob d}
            {s : Γ₁ --> Γ₂}
            (p : y = z)
            (f : internal_morphism_over x y s)
  : internal_morphism_over_to_mor
      (internal_cat_comp_mor_over
         f
         (eq_to_internal_morphism p))
    =
    f.
Proof.
  pose (f' := internal_morphism_over_to_internal_morphism f).
  refine (_ @ maponpaths pr1 (internal_morphism_id_right f')).
  induction p ; cbn.
  apply maponpaths_2.
  use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
  - rewrite PullbackArrow_PullbackPr1.
    apply idpath.
  - rewrite PullbackArrow_PullbackPr2.
    apply assoc.
Qed.

Proposition eq_to_internal_morphism_right
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x y z : Γ --> internal_cat_ob d}
            (p : y = z)
            (f : internal_morphism x y)
  : internal_morphism_to_mor (f ·i eq_to_internal_morphism p) = f.
Proof.
  refine (_ @ maponpaths pr1 (internal_morphism_id_right f)).
  cbn.
  apply maponpaths_2.
  induction p.
  use (PullbackArrowUnique _ (isPullback_Pullback (PB _ _ _ _ _))).
  - rewrite PullbackArrow_PullbackPr1.
    apply idpath.
  - rewrite PullbackArrow_PullbackPr2.
    apply idpath.
Qed.

Proposition idtoiso_disp_eq_to_internal_morphism
            {C : category}
            {PB : Pullbacks C}
            {d : internal_cat PB}
            {Γ : C}
            {x y : Γ --> internal_cat_ob d}
            (p : x = y)
  : pr1 (idtoiso_disp (D := internal_cat_disp_cat d) (idpath _) p)
    =
    eq_to_internal_morphism p.
Proof.
  use internal_morphism_eq.
  induction p ; cbn.
  apply idpath.
Qed.
