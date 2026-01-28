Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.CartesianMonoidal.

Require Import PreservesMonoidalClosed.
Require Import FiberwiseMonoidal.

Local Open Scope cat.

Declare Scope lin_comp_cat.
Local Open Scope lin_comp_cat.

(** * 1. Basic structure *)
Definition linear_comp_cat_structure
  : UU
  := ∑ (C : category)
       (Dcart Dlin : disp_cat C)
       (HDcart : cleaving Dcart)
       (HDlin : cleaving Dlin)
       (χ : disp_functor (functor_identity _ ) Dcart (disp_codomain C)),
     is_cartesian_disp_functor χ
     ×
     disp_functor_ff χ
     ×
     fiberwise_symmetric_monoidal HDlin.

Definition make_linear_comp_cat_structure
           (C : category)
           (Dcart Dlin : disp_cat C)
           (HDcart : cleaving Dcart)
           (HDlin : cleaving Dlin)
           (χ : disp_functor (functor_identity _ ) Dcart (disp_codomain C))
           (H₁ : is_cartesian_disp_functor χ)
           (H₂ : disp_functor_ff χ)
           (H₃ : fiberwise_symmetric_monoidal HDlin)
  : linear_comp_cat_structure
  := C ,, Dcart ,, Dlin ,, HDcart ,, HDlin ,, χ ,, H₁ ,, H₂ ,, H₃.

Coercion linear_comp_cat_ctx
         (C : linear_comp_cat_structure)
  : category
  := pr1 C.

Definition linear_comp_cat_ty
           (C : linear_comp_cat_structure)
  : disp_cat C
  := pr12 C.

Notation "'Ty'" := (linear_comp_cat_ty _) : lin_comp_cat.

Definition linear_comp_cat_lin_ty
           (C : linear_comp_cat_structure)
  : disp_cat C
  := pr122 C.

Notation "'LTy'" := (linear_comp_cat_lin_ty _) : lin_comp_cat.

Definition linear_comp_cat_ty_cleaving
           (C : linear_comp_cat_structure)
  : cleaving (linear_comp_cat_ty C)
  := pr1 (pr222 C).

Definition subst_cart_ty
           {C : linear_comp_cat_structure}
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A : Ty Δ)
  : Ty Γ
  := linear_comp_cat_ty_cleaving C _ _ s A.

Notation "A '[[' s ']]c'" := (subst_cart_ty s A) (at level 20) : lin_comp_cat.

Definition lin_comp_cat_subst
           {C : linear_comp_cat_structure}
           {Γ₁ Γ₂ : C}
           (A : Ty Γ₁)
           (s : Γ₂ --> Γ₁)
  : A[[ s ]]c -->[ s ] A
  := mor_disp_of_cartesian_lift _ _ (linear_comp_cat_ty_cleaving C Γ₁ Γ₂ s A).

Definition linear_comp_cat_lin_ty_cleaving
           (C : linear_comp_cat_structure)
  : cleaving (linear_comp_cat_lin_ty C)
  := pr12 (pr222 C).

Definition subst_lin_ty
           {C : linear_comp_cat_structure}
           {Γ Δ : C}
           (s : Γ --> Δ)
           (A : LTy Δ)
  : LTy Γ
  := linear_comp_cat_lin_ty_cleaving C _ _ s A.

Notation "A '[[' s ']]l'" := (subst_lin_ty s A) (at level 20) : lin_comp_cat.

Definition linear_comp_cat_comprehension
           (C : linear_comp_cat_structure)
  : disp_functor
      (functor_identity _ )
      (linear_comp_cat_ty C)
      (disp_codomain C)
  := pr122 (pr222 C).

Definition linear_comp_cat_extension
           {C : linear_comp_cat_structure}
           (Γ : C)
           (A : Ty Γ)
  : C
  := cod_dom (linear_comp_cat_comprehension C _ A).

Notation "Γ & A" := (linear_comp_cat_extension Γ A) (at level 20) : lin_comp_cat.

Definition linear_comp_cat_pr
           {C : linear_comp_cat_structure}
           {Γ : C}
           (A : Ty Γ)
  : Γ & A --> Γ
  := cod_mor (linear_comp_cat_comprehension C _ A).

Notation "'π'" := linear_comp_cat_pr : lin_comp_cat.

Definition lin_comp_cat_comp_mor
           {C : linear_comp_cat_structure}
           {Γ : C}
           {A B : Ty Γ}
           (s : A -->[ identity _ ] B)
  : Γ & A --> Γ & B
  := dom_mor (♯(linear_comp_cat_comprehension C) s)%mor_disp.

Definition lin_comp_cat_extend_over
           {C : linear_comp_cat_structure}
           {Γ₁ Γ₂ : C}
           (A : Ty Γ₁)
           (s : Γ₂ --> Γ₁)
  : Γ₂ & (A [[ s ]]c) --> Γ₁ & A
  := pr1 (♯(linear_comp_cat_comprehension C) (lin_comp_cat_subst A s))%mor_disp.
           
Definition is_cartesian_linear_comp_cat_comprehension
           (C : linear_comp_cat_structure)
  : is_cartesian_disp_functor
      (linear_comp_cat_comprehension C)
  := pr1 (pr222 (pr222 C)).

Definition is_ff_linear_comp_cat_comprehension
           (C : linear_comp_cat_structure)
  : disp_functor_ff
      (linear_comp_cat_comprehension C)
  := pr12 (pr222 (pr222 C)).

Definition monoidal_linear_comp_cat_lin_ty_cleaving
           (C : linear_comp_cat_structure)
  : fiberwise_symmetric_monoidal
      (linear_comp_cat_lin_ty_cleaving C)
  := pr22 (pr222 (pr222 C)).

(** * 2. Basic type formers *)
Definition cartesian_terminal_type
           (C : linear_comp_cat_structure)
  : UU
  := ∑ (T : fiberwise_terminal (linear_comp_cat_ty_cleaving C)),
     ∏ (Γ : C),
     is_z_isomorphism (π (TerminalObject (pr1 T Γ))).
           
Definition cartesian_initial_type
           (C : linear_comp_cat_structure)
  : UU
  := fiberwise_initial (linear_comp_cat_ty_cleaving C).

Definition cartesian_binproducts_type
           (C : linear_comp_cat_structure)
  : UU
  := fiberwise_binproducts (linear_comp_cat_ty_cleaving C).

Definition cartesian_binproducts_type_cartesian_monoidalcat
           {C : linear_comp_cat_structure}
           (TC : cartesian_terminal_type C)
           (prodC : cartesian_binproducts_type C)
           (Γ : C)
  : monoidal_cat
  := cartesian_monoidalcat
       _
       (pr1 prodC Γ)
       (pr11 TC Γ).

Definition cartesian_binproducts_type_cartesian_monoidalcat_symmetric
           {C : linear_comp_cat_structure}
           (TC : cartesian_terminal_type C)
           (prodC : cartesian_binproducts_type C)
           (Γ : C)
  : symmetric (cartesian_binproducts_type_cartesian_monoidalcat TC prodC Γ)
  := symmetric_cartesian_monoidalcat _ _ _.

Definition cartesian_binproducts_type_symmetric_mon_cat
           {C : linear_comp_cat_structure}
           (TC : cartesian_terminal_type C)
           (prodC : cartesian_binproducts_type C)
           (Γ : C)
  : sym_monoidal_cat
  := cartesian_binproducts_type_cartesian_monoidalcat TC prodC Γ
     ,,
     cartesian_binproducts_type_cartesian_monoidalcat_symmetric TC prodC Γ.

Definition cartesian_bincoproducts_type
           (C : linear_comp_cat_structure)
  : UU
  := fiberwise_bincoproducts (linear_comp_cat_ty_cleaving C).

Definition cartesian_dep_sums
           (C : linear_comp_cat_structure)
  : UU
  := has_dependent_sums (linear_comp_cat_ty_cleaving C).

Section DepSumsProjections.
  Context {C : linear_comp_cat_structure}
          (S : cartesian_dep_sums C)
          {Γ : C}
          (A : Ty Γ).

  Definition cart_dep_sum_cc
             (B : Ty (Γ & A))
    : Ty Γ
    := left_adjoint (pr1 S (Γ & A) Γ (π A)) B.

  Definition cart_dep_sum_unit_cc
             (B : Ty (Γ & A))
    : B -->[ identity _ ] cart_dep_sum_cc B [[ π A ]]c
    := unit_from_right_adjoint (pr1 S (Γ & A) Γ (π A)) B.

  Definition cart_dep_sum_counit_cc
             (B : Ty Γ)
    : cart_dep_sum_cc (B [[ π A ]]c) -->[ identity _ ] B
    := counit_from_right_adjoint (pr1 S (Γ & A) Γ (π A)) B.
End DepSumsProjections.

Definition cartesian_dep_sums_map
           {C : linear_comp_cat_structure}
           (sum : cartesian_dep_sums C)
           {Γ : C}
           (A : Ty Γ)
           (B : Ty (Γ & A))
  : Γ & A & B --> Γ & cart_dep_sum_cc sum A B
  := lin_comp_cat_comp_mor (cart_dep_sum_unit_cc sum A B)
     · lin_comp_cat_extend_over _ _.

Definition strong_cartesian_dep_sums
           (C : linear_comp_cat_structure)
  : UU
  := ∑ (sum : has_dependent_sums (linear_comp_cat_ty_cleaving C)),
     ∏ (Γ : C)
       (A : Ty Γ)
       (B : Ty (Γ & A)),
     is_z_isomorphism (cartesian_dep_sums_map sum A B).

Definition make_strong_cartesian_dep_sums
           (C : linear_comp_cat_structure)
           (sum : has_dependent_sums (linear_comp_cat_ty_cleaving C))
           (HF : ∏ (Γ : C)
                   (A : Ty Γ)
                   (B : Ty (Γ & A)),
                is_z_isomorphism (cartesian_dep_sums_map sum A B))
  : strong_cartesian_dep_sums C
  := sum ,, HF.
           
Definition cartesian_dep_products
           (C : linear_comp_cat_structure)
  : UU
  := has_dependent_products (linear_comp_cat_ty_cleaving C).

Definition linear_terminal_type
           (C : linear_comp_cat_structure)
  : UU
  := fiberwise_terminal (linear_comp_cat_lin_ty_cleaving C).
           
Definition linear_initial_type
           (C : linear_comp_cat_structure)
  : UU
  := fiberwise_initial (linear_comp_cat_lin_ty_cleaving C).

Definition linear_binproducts_type
           (C : linear_comp_cat_structure)
  : UU
  := fiberwise_binproducts (linear_comp_cat_lin_ty_cleaving C).

Definition linear_bincoproducts_type
           (C : linear_comp_cat_structure)
  : UU
  := fiberwise_bincoproducts (linear_comp_cat_lin_ty_cleaving C).

Definition linear_dep_sums
           (C : linear_comp_cat_structure)
  : UU
  := has_dependent_sums (linear_comp_cat_lin_ty_cleaving C).

Section DepLinSumsProjections.
  Context {C : linear_comp_cat_structure}
          (S : linear_dep_sums C)
          {Γ Δ : C}
          (s : Γ --> Δ).

  Definition lin_dep_sum_cc
             (B : LTy Γ)
    : LTy Δ
    := left_adjoint (pr1 S _ _ s) B.

  Definition lin_dep_sum_unit_cc
             (B : LTy Γ)
    : B -->[ identity _ ] lin_dep_sum_cc B [[ s ]]l
    := unit_from_right_adjoint (pr1 S _ _ s) B.

  Definition lin_dep_sum_counit_cc
             (B : LTy Δ)
    : lin_dep_sum_cc (B [[ s ]]l) -->[ identity _ ] B
    := counit_from_right_adjoint (pr1 S _ _ s) B.

  Definition lin_dep_sum_tensor
             (B₁ B₂ : LTy Γ)
    : (fiber_category _ _)
        ⟦ lin_dep_sum_cc
            (monoidal_cat_tensor_pt
               (V := fiber_sym_monoidal_cat
                       (monoidal_linear_comp_cat_lin_ty_cleaving C)
                       _)
               B₁ B₂)
          ,
          monoidal_cat_tensor_pt
            (V := fiber_sym_monoidal_cat
                    (monoidal_linear_comp_cat_lin_ty_cleaving C)
                    _)
            (lin_dep_sum_cc B₁)
            (lin_dep_sum_cc B₂) ⟧
    := left_adjoint_on_tensor
         (V₁ := fiber_sym_monoidal_cat (monoidal_linear_comp_cat_lin_ty_cleaving C) _)
         (V₂ := fiber_sym_monoidal_cat (monoidal_linear_comp_cat_lin_ty_cleaving C) _)
         _
         (is_left_adjoint_left_adjoint (pr1 S _ _ _))
         (strong_sym_monoidal_fiber_functor
            (monoidal_linear_comp_cat_lin_ty_cleaving C)
            s)
         B₁ B₂.
End DepLinSumsProjections.

Definition linear_dep_sums_frobenius_morphism
           {C : linear_comp_cat_structure}
           (sum : linear_dep_sums C)
           {Γ Δ : C}
           (X₁ : LTy Γ)
           (X₂ : LTy Δ)
           (s : Γ --> Δ)
  : (fiber_category _ _)
      ⟦ lin_dep_sum_cc sum
          s
          (monoidal_cat_tensor_pt
             (V := fiber_sym_monoidal_cat
                     (monoidal_linear_comp_cat_lin_ty_cleaving C)
                     _)
             (X₂ [[ s ]]l)
             X₁)
        ,
        monoidal_cat_tensor_pt
          (V := fiber_sym_monoidal_cat
                  (monoidal_linear_comp_cat_lin_ty_cleaving C)
                  _)
          X₂
          (lin_dep_sum_cc sum s X₁) ⟧
  := lin_dep_sum_tensor _ _ _ _
     · rightwhiskering_on_morphisms
         (fiber_sym_monoidal_cat
            (monoidal_linear_comp_cat_lin_ty_cleaving C)
            _)
         _ _ _
         (lin_dep_sum_counit_cc _ _ _).

Definition linear_dep_sums_frobenius
           (C : linear_comp_cat_structure)
  : UU
  := ∑ (sum : has_dependent_sums (linear_comp_cat_lin_ty_cleaving C)),
     ∏ (Γ Δ : C)
       (X₁ : LTy Γ)
       (X₂ : LTy Δ)
       (s : Γ --> Δ),
     is_z_isomorphism (linear_dep_sums_frobenius_morphism sum X₁ X₂ s).

Definition make_linear_dep_sums_frobenius
           (C : linear_comp_cat_structure)
           (sum : has_dependent_sums (linear_comp_cat_lin_ty_cleaving C))
           (H : ∏ (Γ Δ : C)
                  (X₁ : LTy Γ)
                  (X₂ : LTy Δ)
                  (s : Γ --> Δ),
                is_z_isomorphism (linear_dep_sums_frobenius_morphism sum X₁ X₂ s))
  : linear_dep_sums_frobenius C
  := sum ,, H.
           
Definition linear_dep_products
           (C : linear_comp_cat_structure)
  : UU
  := has_dependent_products (linear_comp_cat_lin_ty_cleaving C).

Definition fiber_monoidal_closed
           (C : linear_comp_cat_structure)
  : UU
  := ∏ (Γ : C),
     monoidal_leftclosed
       (fiber_sym_monoidal_cat
          (monoidal_linear_comp_cat_lin_ty_cleaving C) Γ).

Definition fiber_sym_mon_closed_cat
           {C : linear_comp_cat_structure}
           (F : fiber_monoidal_closed C)
           (Γ : C)
  : sym_mon_closed_cat
  := fiber_sym_monoidal_cat (monoidal_linear_comp_cat_lin_ty_cleaving C) Γ ,, F Γ.

Definition linear_function_types
           (C : linear_comp_cat_structure)
  : UU
  := ∑ (F : fiber_monoidal_closed C),
     ∏ (Γ Δ : C)
       (s : Γ --> Δ),
     @preserves_sym_mon_closed
       (fiber_sym_mon_closed_cat F Δ)
       (fiber_sym_mon_closed_cat F Γ)
       (strong_sym_monoidal_fiber_functor
          (monoidal_linear_comp_cat_lin_ty_cleaving C)
          s).

Definition linear_non_linear_type
           {C : linear_comp_cat_structure}
           (TC : cartesian_terminal_type C)
           (prodC : cartesian_binproducts_type C)
  : UU
  := ∑ (L : disp_adjunction_id
              (linear_comp_cat_ty C)
              (linear_comp_cat_lin_ty C)),
     is_cartesian_disp_functor (left_adj_over_id L)
     ×
     is_cartesian_disp_functor (right_adj_over_id L)
     ×
     ∏ (Γ : C),
     ∑ (HL : fmonoidal
               (cartesian_binproducts_type_symmetric_mon_cat TC prodC Γ)
               (fiber_sym_monoidal_cat
                  (monoidal_linear_comp_cat_lin_ty_cleaving C)
                  _)
               (fiber_functor (left_adj_over_id L) Γ)),
     is_symmetric_monoidal_functor
       (cartesian_binproducts_type_symmetric_mon_cat TC prodC Γ)
       (fiber_sym_monoidal_cat
          (monoidal_linear_comp_cat_lin_ty_cleaving C)
          _)
       HL.

(** 3. Linear comprehension categories *)
Definition linear_comp_cat_types
           (C : linear_comp_cat_structure)
  : UU
  := cartesian_initial_type C
     ×
     cartesian_bincoproducts_type C
     ×
     strong_cartesian_dep_sums C
     ×
     cartesian_dep_products C
     ×
     linear_terminal_type C
     ×
     linear_initial_type C
     ×
     linear_binproducts_type C
     ×
     linear_bincoproducts_type C
     ×
     linear_dep_sums_frobenius C
     ×
     linear_function_types C
     ×
     linear_dep_products C.
           
Definition linear_comp_cat
  : UU
  := ∑ (C : linear_comp_cat_structure),
     linear_comp_cat_types C
     ×
     ∑ (TC : cartesian_terminal_type C)
       (prodC : cartesian_binproducts_type C),
    linear_non_linear_type TC prodC.

Definition make_linear_comp_cat
           (C : linear_comp_cat_structure)
           (tys : linear_comp_cat_types C)
           (TC : cartesian_terminal_type C)
           (prodC : cartesian_binproducts_type C)
           (lnl : linear_non_linear_type TC prodC)
  : linear_comp_cat
  := C ,, tys ,, TC ,, prodC ,, lnl.
