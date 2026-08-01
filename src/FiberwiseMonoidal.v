(**

 Fiberwise monoidal structures for displayed categories

 In this file, we define it when a displayed category is equipped with a fiberwise
 monoidal structure. Specifically, this entails to the following data:
 - a monoidal structure on every fiber category
 - a lax monoidal structure on every fiber functor
 and there should be proofs that the natural isomorphisms witnessing the preservation
 of the identity and composition should be monoidal transformations. We provide the
 basic definitions for these notions in this file.

 Contents
 1. Fiberwise monoidal structures
 2. Fiberwise symmetric monoidal structures

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.

(** * 1. Fiberwise monoidal structures *)
Definition fiberwise_monoidal_data
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := ∑ (M : ∏ (x : C), monoidal (D[{x}])),
     ∏ (x y : C)
       (f : x --> y),
     fmonoidal
       (M y) (M x)
       (fiber_functor_from_cleaving D HD f).

Definition make_fiberwise_monoidal_data
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
           (M : ∏ (x : C), monoidal (D[{x}]))
           (HM : ∏ (x y : C)
                   (f : x --> y),
                 fmonoidal
                   (M y) (M x)
                   (fiber_functor_from_cleaving D HD f))
  : fiberwise_monoidal_data HD
  := M ,, HM.

Section LocallyPropositionalFiberwiseMonoidal.
  Context {C : category}
          {D : disp_cat C}
          {HD : cleaving D}
          (HD' : locally_propositional D)
          (m : ∏ (x : C), D x → D x → D x)
          (ml : ∏ (x : C)
                  (b a₁ a₂ : D x),
                a₁ -->[ identity _ ] a₂
                →
                m x a₁ b -->[ identity _ ] m x a₂ b)
          (mr : ∏ (x : C)
                  (a b₁ b₂ : D x),
                b₁ -->[ identity _ ] b₂
                →
                m x a b₁ -->[ identity _ ] m x a b₂)
          (u : ∏ (x : C), D x)
          (l : ∏ (x : C)
                 (b : D x),
               m x (u x) b -->[ identity _ ] b)
          (linv : ∏ (x : C)
                    (b : D x),
                  b -->[ identity _ ] m x (u x) b)
          (r : ∏ (x : C)
                 (a : D x),
               m x a (u x) -->[ identity _ ] a)
          (rinv : ∏ (x : C)
                    (a : D x),
                  a -->[ identity _ ] m x a (u x))
          (assocl : ∏ (x : C)
                      (a b c : D x),
                     m x (m x a b) c -->[ identity _ ] m x a (m x b c))
          (assocr : ∏ (x : C)
                      (a b c : D x),
                    m x a (m x b c) -->[ identity _ ] m x (m x a b) c)
          (subm : ∏ (x y : C)
                    (f : x --> y)
                    (a b : D y),
                  m x (HD y x f a) (HD y x f b)
                  -->[ identity _ ]
                  pr1 (HD y x f (m y a b)))
          (subminv : ∏ (x y : C)
                       (f : x --> y)
                       (a b : D y),
                     pr1 (HD y x f (m y a b))
                     -->[ identity _ ]
                     m x (HD y x f a) (HD y x f b))
          (subu : ∏ (x y : C)
                    (f : x --> y),
                  u x
                  -->[ identity _ ]
                  pr1 (HD y x f (u y)))
          (subuinv : ∏ (x y : C)
                       (f : x --> y),
                     pr1 (HD y x f (u y))
                     -->[ identity _ ]
                     u x).
  
  Definition make_fiberwise_monoidal_data_locally_propositional_monoidal_data
             (x : C)
    : monoidal_data (D[{x}]).
  Proof.
    simple refine ((_ ,, _ ,, _) ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact (m x).
    - exact (mr x).
    - exact (ml x).
    - exact (u x).
    - exact (l x).
    - exact (linv x).
    - exact (r x).
    - exact (rinv x).
    - exact (assocl x).
    - exact (assocr x).
  Defined.
  
  Definition make_fiberwise_monoidal_data_locally_propositional_monoidal
             (x : C)
    : monoidal (D[{x}]).
  Proof.
    simple refine (_ ,, _).
    - exact (make_fiberwise_monoidal_data_locally_propositional_monoidal_data x).
    - abstract
        (repeat split ; try (intro ; intros) ; apply HD').
  Defined.

  Definition make_fiberwise_monoidal_data_locally_propositional_fmonoidal_data
             {x y : C}
             (f : x --> y)
    : fmonoidal_data
        (make_fiberwise_monoidal_data_locally_propositional_monoidal y)
        (make_fiberwise_monoidal_data_locally_propositional_monoidal x)
        (fiber_functor_from_cleaving D HD f).
  Proof.
    simple refine (_ ,, _).
    - exact (subm x y f).
    - exact (subu x y f).
  Defined.

  Definition make_fiberwise_monoidal_data_locally_propositional_fmonoidal_lax
             {x y : C}
             (f : x --> y)
    : fmonoidal_lax
        (make_fiberwise_monoidal_data_locally_propositional_monoidal y)
        (make_fiberwise_monoidal_data_locally_propositional_monoidal x)
        (fiber_functor_from_cleaving D HD f).
  Proof.
    simple refine (_ ,, _).
    - exact (make_fiberwise_monoidal_data_locally_propositional_fmonoidal_data f).
    - abstract
        (repeat split ; try (intro ; intros) ; apply HD').
  Defined.

  Definition make_fiberwise_monoidal_data_locally_propositional_fmonoidal
             {x y : C}
             (f : x --> y)
    : fmonoidal
        (make_fiberwise_monoidal_data_locally_propositional_monoidal y)
        (make_fiberwise_monoidal_data_locally_propositional_monoidal x)
        (fiber_functor_from_cleaving D HD f).
  Proof.
    simple refine (_ ,, _).
    - exact (make_fiberwise_monoidal_data_locally_propositional_fmonoidal_lax f).
    - split.
      + intros a b.
        refine (subminv x y f a b ,, _).
        abstract (split ; apply HD').
      + refine (subuinv x y f ,, _).
        abstract (split ; apply HD').
  Defined.
  
  Definition make_fiberwise_monoidal_data_locally_propositional         
    : fiberwise_monoidal_data HD.
  Proof.
    use make_fiberwise_monoidal_data.
    - exact make_fiberwise_monoidal_data_locally_propositional_monoidal.
    - intros x y f.
      exact (make_fiberwise_monoidal_data_locally_propositional_fmonoidal f).
  Defined.
End LocallyPropositionalFiberwiseMonoidal.

Definition fiber_monoidal
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_monoidal_data HD)
           (x : C)
  : monoidal (D[{x}])
  := pr1 M x.
           
Definition fiber_monoidal_cat
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_monoidal_data HD)
           (x : C)
  : monoidal_cat
  := D[{x}] ,, fiber_monoidal M x.

Coercion fiber_monoidal_cat : fiberwise_monoidal_data >-> Funclass.

Definition fiber_functor_strong_monoidal_structure
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_monoidal_data HD)
           {x y : C}
           (f : x --> y)
  : fmonoidal (M y) (M x) (fiber_functor_from_cleaving D HD f)
  := pr2 M x y f.

Definition strong_monoidal_fiber_functor
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_monoidal_data HD)
           {x y : C}
           (f : x --> y)
  : strong_monoidal_functor (M y) (M x)
  := fiber_functor_from_cleaving D HD f
     ,,
     fiber_functor_strong_monoidal_structure M f.

Definition fiberwise_monoidal_laws
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_monoidal_data HD)
  : UU
  := (∏ (x : C),
      is_mon_nat_trans
        (identity_fmonoidal _)
        (fiber_functor_strong_monoidal_structure M (identity _))
        (fiber_functor_from_cleaving_identity HD x))
     ×
     (∏ (x y z : C)
        (f : x --> y)
        (g : y --> z),
      is_mon_nat_trans
        (comp_fmonoidal
           (fiber_functor_strong_monoidal_structure M g)
           (fiber_functor_strong_monoidal_structure M f))
        (fiber_functor_strong_monoidal_structure M (f · g))
        (fiber_functor_from_cleaving_comp HD g f)).

Proposition fiberwise_monoidal_laws_locally_propositional
            {C : category}
            {D : disp_cat C}
            {HD : cleaving D}
            (HD' : locally_propositional D)
            (M : fiberwise_monoidal_data HD)
  : fiberwise_monoidal_laws M.
Proof.
  split ; intro ; intros ; split ; try (intro ; intros) ; apply HD'.
Qed.

Definition fiberwise_monoidal
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := ∑ (M : fiberwise_monoidal_data HD), fiberwise_monoidal_laws M.

Definition make_fiberwise_monoidal
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
           (M : fiberwise_monoidal_data HD)
           (HM : fiberwise_monoidal_laws M)
  : fiberwise_monoidal HD
  := M ,, HM.

Definition make_fiberwise_monoidal_locally_propositional
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
           (HD' : locally_propositional D)
           (M : fiberwise_monoidal_data HD)
  : fiberwise_monoidal HD
  := M ,, fiberwise_monoidal_laws_locally_propositional HD' M.

Coercion fiberwise_monoidal_to_data
         {C : category}
         {D : disp_cat C}
         {HD : cleaving D}
         (M : fiberwise_monoidal HD)
  : fiberwise_monoidal_data HD
  := pr1 M.

Proposition strong_monoidal_cleaving_identity
            {C : category}
            {D : disp_cat C}
            {HD : cleaving D}
            (M : fiberwise_monoidal HD)
            (x : C)
  : is_mon_nat_trans
      (identity_fmonoidal _)
      (strong_monoidal_fiber_functor M (identity _))
      (fiber_functor_from_cleaving_identity HD x).
Proof.
  exact (pr12 M x).
Defined.

Proposition strong_monoidal_cleaving_comp
            {C : category}
            {D : disp_cat C}
            {HD : cleaving D}
            (M : fiberwise_monoidal HD)
            {x y z : C}
            (f : x --> y)
            (g : y --> z)
  : is_mon_nat_trans
      (comp_fmonoidal
         (fiber_functor_strong_monoidal_structure M g)
         (fiber_functor_strong_monoidal_structure M f))
      (strong_monoidal_fiber_functor M (f · g))
      (fiber_functor_from_cleaving_comp HD g f).
Proof.
  exact (pr22 M x y z f g).
Defined.

(** * 2. Fiberwise symmetric monoidal structures *)
Definition fiberwise_symmetric_monoidal_structure
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_monoidal HD)
  : UU
  := ∑ (S : ∏ (x : C), symmetric (M x)),
     ∏ (x y : C)
       (f : x --> y),
     is_symmetric_monoidal_functor (S y) (S x) (strong_monoidal_fiber_functor M f).

Definition make_fiberwise_symmetric_monoidal_structure
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_monoidal HD)
           (S : ∏ (x : C), symmetric (M x))
           (Sf : ∏ (x y : C)
                   (f : x --> y),
                 is_symmetric_monoidal_functor
                   (S y) (S x)
                   (strong_monoidal_fiber_functor M f))
  : fiberwise_symmetric_monoidal_structure M
  := S ,, Sf.

Section SymmetricLocallyPropositional.
  Context {C : category}
          {D : disp_cat C}
          {HD : cleaving D}
          (HD' : locally_propositional D)
          (M : fiberwise_monoidal HD)
          (sym : ∏ (x : C)
                   (a b : M x),
                monoidal_cat_tensor_pt a b --> monoidal_cat_tensor_pt b a).
          
  Definition make_fiberwise_symmetric_monoidal_structure_locally_propositional_sym
             (x : C)
    : symmetric (M x).
  Proof.
    use make_symmetric.
    - exact (sym x).
    - abstract
        (repeat split ; intros ; apply HD').
  Defined.
  
  Definition make_fiberwise_symmetric_monoidal_structure_locally_propositional               
    : fiberwise_symmetric_monoidal_structure M.
  Proof.
    use make_fiberwise_symmetric_monoidal_structure.
    - exact make_fiberwise_symmetric_monoidal_structure_locally_propositional_sym.
    - abstract
        (intros x y f ;
         intros a b ;
         apply HD').
  Defined.
End SymmetricLocallyPropositional.

Definition fiber_monoidal_symmetric
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {M : fiberwise_monoidal HD}
           (S : fiberwise_symmetric_monoidal_structure M)
           (x : C)
  : symmetric (M x)
  := pr1 S x.

Definition is_symmetric_fiber_functor_strong_monoidal_structure
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {M : fiberwise_monoidal HD}
           (S : fiberwise_symmetric_monoidal_structure M)
           {x y : C}
           (f : x --> y)
  : is_symmetric_monoidal_functor
      (fiber_monoidal_symmetric S y)
      (fiber_monoidal_symmetric S x)
      (strong_monoidal_fiber_functor M f)
  := pr2 S x y f.

Definition fiberwise_symmetric_monoidal
           {C : category}
           {D : disp_cat C}
           (HD : cleaving D)
  : UU
  := ∑ (M : fiberwise_monoidal HD), fiberwise_symmetric_monoidal_structure M.

Definition make_fiberwise_symmetric_monoidal
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_monoidal HD)
           (S : fiberwise_symmetric_monoidal_structure M)
  : fiberwise_symmetric_monoidal HD
  := M ,, S.

Definition fiber_sym_monoidal_cat
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_symmetric_monoidal HD)
           (x : C)
  : sym_monoidal_cat
  := (D[{x}] ,, _) ,, fiber_monoidal_symmetric (pr2 M) x.

Coercion fiber_sym_monoidal_cat : fiberwise_symmetric_monoidal >-> Funclass.

Definition strong_sym_monoidal_fiber_functor
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (M : fiberwise_symmetric_monoidal HD)
           {x y : C}
           (f : x --> y)
  : symmetric_strong_monoidal_functor (M y) (M x).
Proof.
  use make_symmetric_strong_monoidal_functor.
  - exact (strong_monoidal_fiber_functor (pr1 M) f).
  - exact (pr22 M x y f).
Defined.

Proposition strong_sym_monoidal_cleaving_identity
            {C : category}
            {D : disp_cat C}
            {HD : cleaving D}
            (M : fiberwise_symmetric_monoidal HD)
            (x : C)
  : is_mon_nat_trans
      (identity_fmonoidal_lax _)
      (strong_sym_monoidal_fiber_functor M (identity _))
      (fiber_functor_from_cleaving_identity HD x).
Proof.
  exact (strong_monoidal_cleaving_identity (pr1 M) x).
Defined.

Proposition strong_sym_monoidal_cleaving_comp
            {C : category}
            {D : disp_cat C}
            {HD : cleaving D}
            (M : fiberwise_symmetric_monoidal HD)
            {x y z : C}
            (f : x --> y)
            (g : y --> z)
  : is_mon_nat_trans
      (comp_fmonoidal_lax
         (strong_sym_monoidal_fiber_functor M g)
         (strong_sym_monoidal_fiber_functor M f))
      (strong_sym_monoidal_fiber_functor M (f · g))
      (fiber_functor_from_cleaving_comp HD g f).
Proof.
  exact (strong_monoidal_cleaving_comp (pr1 M) f g).
Defined.
