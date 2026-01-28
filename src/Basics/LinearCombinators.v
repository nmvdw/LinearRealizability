(**

 Derived combinators for linear combinatory algebras

 In this file, we derive various useful combinators for linear combinatory algebras.

 Contents
 1. Composition (for linear assemblies)

 *)
Require Import UniMath.MoreFoundations.All.

Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Combinators.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCompleteness.

Local Open Scope lca.

Ltac calc_subst_eq :=
  match goal with
  | [ |- closed_lin_term_eval (_ {{ _ ↦ _ }}) _ = _ ]
    => refine (closed_lin_term_eval_eq _ _) ;
       calc_subst_eq
  | [ |- (Λl _) {{ _ ↦ _ }} = _ ]
    => rewrite lam_lin_term_linear_subst ;
       refine (lam_lin_term_linear_eq _ _) ;
       calc_subst_eq
  | [ |- (Λn _) {{ _ ↦ _ }} = _ ]
    => rewrite lam_lin_term_nonlinear_subst ;
       apply maponpaths ;
       calc_subst_eq
  | _ => cbn ; apply idpath
  end.

Ltac calc_subst :=
  match goal with
  | [ |- _ · _ = _ ] => apply maponpaths_2 ; calc_subst
  | _ => calc_subst_eq
  end.

Ltac calc_beta_step :=
  match goal with
  | [ |- closed_lin_term_eval (Λl _) _ · _ = _ ] =>
      rewrite lam_lin_term_beta' ;
      calc_subst
  | [ |- closed_lin_term_eval (Λn _) _ · _ = _ ] =>
      rewrite lam_lin_term_nonlinear_beta' ;
      calc_subst
  | [ |- _ · _ = _ ] => apply maponpaths_2 ; calc_beta_step
  end.

Ltac calc_beta :=
  repeat (etrans ; [ calc_beta_step | ]) ; cbn ; try (apply idpath).
      
(** * 1. Composition (for linear assemblies) *)
Definition lin_dep_comp
           (A : linear_combinatory_algebra)
  : A.
Proof.
  pose (t := V 4 • (Co F • V 2 • (Co δ • V 1)) • (V 3 • V 1 • V 0) : lin_term A).
  simple refine (closed_lin_term_eval (Λl (Λl (Λn (Λn (Λl t))))) _) ;
    unfold t ;
    check_linear_lam.
Defined.

Notation "'Bd'" := (lin_dep_comp _) : lca.

Proposition lin_dep_comp_eq
            {A : linear_combinatory_algebra}
            {f g s x xx : A}
  : Bd · f · g · (!s) · (!x) · xx = f · (!(s · !x)) · (g · (!x) · xx).
Proof.
  unfold lin_dep_comp.
  calc_beta.
  rewrite linear_combinatory_algebra_delta_eq.
  rewrite linear_combinatory_algebra_f_eq.
  apply idpath.
Qed.    


Definition lin_pair_combinator
           (A : linear_combinatory_algebra)
  : A.
Proof.
  pose (t := V 0 • V 2 • V 1 : lin_term A).
  simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;
    unfold t ;
    check_linear_lam.
Defined.

Notation "'lin_pair'" := (lin_pair_combinator _) : lca.

Proposition lin_dep_pair_eq
            {A : linear_combinatory_algebra}
            {p q x : A}
  : lin_pair · p · q · x = x · p · q.
Proof.
  unfold lin_pair_combinator.
  calc_beta.
Qed.    


Definition lca_let_combinator_help
           (A : linear_combinatory_algebra)
  : A.
Proof.
  pose (t := V 2 • V 1 • V 0 : lin_term A).
  simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_let_combinator_help_eq
            {A : linear_combinatory_algebra}
            {r u v : A}
  : lca_let_combinator_help A · r · u · v = r · u · v.
Proof.
  unfold lca_let_combinator_help.
  calc_beta.
Qed.    

Definition lca_let_combinator
           (A : linear_combinatory_algebra)
  : A.
Proof.
  pose (t := V 1 • (Co (lca_let_combinator_help A) • V 0)).
  simple refine (closed_lin_term_eval (Λl (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.
  
Notation "'lca_let'" := (lca_let_combinator _) : lca.

Proposition lca_let_combinator_eq
            {A : linear_combinatory_algebra}
            {r u v : A}
  : lca_let · (lin_pair · u · v) · r = r · u · v.
Proof.
  unfold lca_let_combinator.
  calc_beta.
  rewrite lin_dep_pair_eq.
  rewrite lca_let_combinator_help_eq.
  apply idpath.
Qed.

Definition lca_swap_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lin_pair • V 0 • V 1 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_swap_help_eq
            {A : linear_combinatory_algebra}
            {u v : A}
  : lca_swap_help · u · v = lin_pair · v · u.
Proof.
  unfold lca_swap_help.
  calc_beta.
Qed.

Definition lca_swap
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • Co lca_swap_help : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl t) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_swap_combinator_eq
            {A : linear_combinatory_algebra}
            {u v : A}
  : lca_swap · (lin_pair · u · v) = lin_pair · v · u.
Proof.
  unfold lca_swap.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite lca_swap_help_eq.
  apply idpath.
Qed.

Definition lca_lwhisker_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lin_pair • V 1 • (V 3 • V 2 • V 0) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl (Λl t)))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_lwhisker_help_eq
            {A : linear_combinatory_algebra}
            (a x u v : A)
  : lca_lwhisker_help · a · x · u · v
    =
    lin_pair · u · (a · x · v).
Proof.
  unfold lca_lwhisker_help.
  calc_beta.
Qed.
  
Definition lca_lwhisker
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_lwhisker_help • V 2 • V 1) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_lwhisker_eq
            {A : linear_combinatory_algebra}
            (a x u v : A)
  : lca_lwhisker · a · x · (lin_pair · u · v)
    =
    lin_pair · u · (a · x · v).
Proof.
  unfold lca_lwhisker.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite lca_lwhisker_help_eq.
  apply idpath.
Qed.
  
Definition lca_rwhisker_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lin_pair • (V 3 • V 2 • V 1) • V 0 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl (Λl t)))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_rwhisker_help_eq
            {A : linear_combinatory_algebra}
            (a x u v : A)
  : lca_rwhisker_help · a · x · u · v
    =
    lin_pair · (a · x · u) · v.
Proof.
  unfold lca_rwhisker_help.
  calc_beta.
Qed.
  
Definition lca_rwhisker
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_rwhisker_help • V 2 • V 1) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_rwhisker_eq
            {A : linear_combinatory_algebra}
            (a x u v : A)
  : lca_rwhisker · a · x · (lin_pair · u · v)
    =
    lin_pair · (a · x · u) · v.
Proof.
  unfold lca_rwhisker.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite lca_rwhisker_help_eq.
  apply idpath.
Qed.
  

Definition lca_lunitor
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • Co I : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_lunitor_eq
            {A : linear_combinatory_algebra}
            {x y z : A}
  : lca_lunitor · (!x) · (lin_pair · y · z) = y · z.
Proof.
  unfold lca_lunitor.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite linear_combinatory_algebra_i_eq.
  apply idpath.
Qed.

Definition lca_runitor
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • Co (C · I) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_runitor_eq
            {A : linear_combinatory_algebra}
            {x y z : A}
  : lca_runitor · (!x) · (lin_pair · y · z) = z · y.
Proof.
  unfold lca_runitor.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite linear_combinatory_algebra_c_eq.
  rewrite linear_combinatory_algebra_i_eq.
  apply idpath.
Qed.


Definition lca_assoc_left_help_2
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lin_pair • V 1 • (Co lin_pair • V 0 • V 2) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_assoc_left_help_2_eq
            {A : linear_combinatory_algebra}
            {x y z : A}
  : lca_assoc_left_help_2 · z · x · y
    =
    lin_pair · x · (lin_pair · y · z).
Proof.
  unfold lca_assoc_left_help_2.
  calc_beta.
Qed.

Definition lca_assoc_left_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_assoc_left_help_2 • V 1) : lin_term A) as t. 
  simple refine (closed_lin_term_eval (Λl (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_assoc_left_help_eq
            {A : linear_combinatory_algebra}
            {x y z : A}
  : lca_assoc_left_help · z · (lin_pair · x · y)
    =
    lin_pair · x · (lin_pair · y · z).
Proof.
  unfold lca_assoc_left_help.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite lca_assoc_left_help_2_eq.
  apply idpath.
Qed.

Definition lca_assoc_left
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co (C · lca_assoc_left_help) : lin_term A)) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_assoc_left_eq
            {A : linear_combinatory_algebra}
            {w x y z : A}
  : lca_assoc_left · (!w) · (lin_pair · (lin_pair · x · y) · z)
    =
    lin_pair · x · (lin_pair · y · z).
Proof.
  unfold lca_assoc_left.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite linear_combinatory_algebra_c_eq.
  rewrite lca_assoc_left_help_eq.
  apply idpath.
Qed.

Definition lca_assoc_right_help_2
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lin_pair • (Co lin_pair • V 2 • V 1) • V 0 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_assoc_right_help_2_eq
            {A : linear_combinatory_algebra}
            {x y z : A}
  : lca_assoc_right_help_2 · x · y · z
    =
    lin_pair · (lin_pair · x · y) · z.
Proof.
  unfold lca_assoc_right_help_2.
  calc_beta.
Qed.

Definition lca_assoc_right_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_assoc_right_help_2 • V 1) : lin_term A) as t. 
  simple refine (closed_lin_term_eval (Λl (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_assoc_right_help_eq
            {A : linear_combinatory_algebra}
            {x y z : A}
  : lca_assoc_right_help · x · (lin_pair · y · z)
    =
    lin_pair · (lin_pair · x · y) · z.
Proof.
  unfold lca_assoc_right_help.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite lca_assoc_right_help_2_eq.
  apply idpath.
Qed.

Definition lca_assoc_right
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_assoc_right_help : lin_term A)) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_assoc_right_eq
            {A : linear_combinatory_algebra}
            {w x y z : A}
  : lca_assoc_right · (!w) · (lin_pair · x · (lin_pair · y · z))
    =
    lin_pair · (lin_pair · x · y) · z.
Proof.
  unfold lca_assoc_right.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite lca_assoc_right_help_eq.
  apply idpath.
Qed.


Definition lca_del_2
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (V 2 • V 1 • (Co D • V 0) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_del_2_eq
            {A : linear_combinatory_algebra}
            {a b₁ b₂ : A}
  : lca_del_2 · a · b₁ · (!b₂)
    =
    a · b₁ · b₂.
Proof.
  unfold lca_del_2.
  calc_beta.
  rewrite linear_combinatory_algebra_d_eq.
  apply idpath.
Qed.


Definition lca_F_2
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co F • (Co F • V 2 • Excl (V 1)) • Excl (V 0) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λn (Λn t))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_F_2_eq
            {A : linear_combinatory_algebra}
            {a b₁ b₂ : A}
  : lca_F_2 · (!a )· (!b₁) · (!b₂)
    =
    !(a · (!b₁) · !b₂).
Proof.
  unfold lca_F_2.
  calc_beta.
  rewrite !linear_combinatory_algebra_f_eq.
  apply idpath.
Qed.


Section LinearNonLinear.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  Definition lca_lnl_f
    : A.
  Proof.
    pose (V 2
          • (Excl (Co (π₁%ca : AC) • V 1))
          • (Co lin_pair • (Excl (Co (π₂%ca : AC) • V 1)) • V 0) : lin_term A) as t.
    simple refine (closed_lin_term_eval (Λl (Λn (Λl t))) _) ;  
      unfold t ;
      check_linear_lam.
  Defined.

  Proposition lca_lnl_f_eq
              {a b₁ b₂ : A}
    : lca_lnl_f · a · (!b₁) · b₂
      =
      a · (!((π₁%ca : AC) · b₁)) · (lin_pair · (!((π₂%ca : AC) · b₁)) · b₂).
  Proof.
    unfold lca_lnl_f.
    calc_beta.
  Qed.

  Definition lca_lnl_b_help
    : A.
  Proof.
    pose (V 3 • (Excl (Co (pair%ca : AC) • V 2 • V 1)) • V 0) as t.
    simple refine (closed_lin_term_eval (Λl (Λn (Λn (Λl t)))) _) ;  
      unfold t ;
      check_linear_lam.
  Defined.

  Proposition lca_lnl_b_help_eq
              {a b c₁ c₂ : A}
    : lca_lnl_b_help · a · (!b) · (!c₁) · c₂
      =
      a · (!((pair%ca : AC) · b · c₁)) · c₂.
  Proof.
    unfold lca_lnl_b_help.
    calc_beta.
  Qed.

  Definition lca_lnl_b
    : A.
  Proof.
    pose (Co lca_let • V 0 • (Co lca_lnl_b_help • V 2 • V 1)) as t.
    simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;  
      unfold t ;
      check_linear_lam.
  Defined.

  Proposition lca_lnl_b_eq
              {a b c₁ c₂ : A}
    : lca_lnl_b · a · (!b) · (lin_pair · (!c₁) · c₂)
      =
      (a · (!((pair%ca : AC) · b · c₁)) · c₂)%lca.
  Proof.
    unfold lca_lnl_b.
    calc_beta.
    rewrite lca_let_combinator_eq.
    rewrite lca_lnl_b_help_eq.
    apply idpath.
  Qed.
End LinearNonLinear.

Definition lca_D_Ks
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co D • V 0 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_D_Ks_eq
            {A : linear_combinatory_algebra}
            {a₁ a₂ : A}
  : lca_D_Ks · (!a₁) · (!a₂) = a₂.
Proof.
  unfold lca_D_Ks.
  calc_beta.
  rewrite linear_combinatory_algebra_d_eq.
  apply idpath.
Qed.

Definition lca_D_K
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co D • V 1 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λn t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_D_K_eq
            {A : linear_combinatory_algebra}
            {a₁ a₂ : A}
  : lca_D_K · (!a₁) · (!a₂) = a₁.
Proof.
  unfold lca_D_K.
  calc_beta.
  rewrite linear_combinatory_algebra_d_eq.
  apply idpath.
Qed.

Definition lca_binprod_pr1_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • Co lca_D_K • V 1 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Definition lca_binprod_pr2_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • Co lca_D_Ks • V 1 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Definition lca_binprod_pr1
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_binprod_pr1_help) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Definition lca_binprod_pr2
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_binprod_pr2_help) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_binprod_pr1_eq
            {A : linear_combinatory_algebra}
            {a b c₁ c₂ : A}
  : lca_binprod_pr1 · (!a) · (lin_pair · b · (lin_pair · (!c₁) · (!c₂))) = c₁ · b.
Proof.
  unfold lca_binprod_pr1.
  calc_beta.
  rewrite lca_let_combinator_eq.
  unfold lca_binprod_pr1_help.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite lca_D_K_eq.
  apply idpath.
Qed.

Proposition lca_binprod_pr2_eq
            {A : linear_combinatory_algebra}
            {a b c₁ c₂ : A}
  : lca_binprod_pr2 · (!a) · (lin_pair · b · (lin_pair · (!c₁) · (!c₂))) = c₂ · b.
Proof.
  unfold lca_binprod_pr2.
  calc_beta.
  rewrite lca_let_combinator_eq.
  unfold lca_binprod_pr2_help.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite lca_D_Ks_eq.
  apply idpath.
Qed.

Definition lca_binprod_pair
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lin_pair
        • V 0
        • (Co lin_pair
           • (Co F • V 3 • Excl (V 1))
           • (Co F • V 2 • Excl (V 1))) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λn (Λn (Λl t)))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_binprod_pair_eq
            {A : linear_combinatory_algebra}
            {a₁ a₂ b₁ b₂ : A}
  : lca_binprod_pair · (!a₁) · (!a₂) · (!b₁) · b₂
    =
    lin_pair · b₂ · (lin_pair · (!(a₁ · !b₁)) · (!(a₂ · !b₁))).
Proof.
  unfold lca_binprod_pair.
  calc_beta.
  rewrite !linear_combinatory_algebra_f_eq.
  apply idpath.
Qed.

Definition lca_bincoprod_left
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose ((Co D • V 1) • V 2 • V 0 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl (Λl (Λl t)))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_bincoprod_left_eq
            {A : linear_combinatory_algebra}
            {a₁ a₂ b₁ b₂ : A}
  : lca_bincoprod_left · (!a₂) · b₁ · (!a₁) · b₂ = a₁ · b₁ · b₂.
Proof.
  unfold lca_bincoprod_left.
  calc_beta.
  rewrite linear_combinatory_algebra_d_eq.
  apply idpath.
Qed.

Definition lca_bincoprod_right
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose ((Co D • V 3) • V 2 • V 0 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λn (Λl t)))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_bincoprod_right_eq
            {A : linear_combinatory_algebra}
            {a₁ a₂ b₁ b₂ : A}
  : lca_bincoprod_right · (!a₂) · b₁ · (!a₁) · b₂ = a₂ · b₁ · b₂.
Proof.
  unfold lca_bincoprod_right.
  calc_beta.
  rewrite linear_combinatory_algebra_d_eq.
  apply idpath.
Qed.

Definition lca_bincoprod_inl
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co (lin_pair · lca_bincoprod_left) • V 0 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_bincoprod_inl_eq
            {A : linear_combinatory_algebra}
            {a₁ a₂ : A}
  : lca_bincoprod_inl · (!a₁) · a₂
    =
    lin_pair · lca_bincoprod_left · a₂.
Proof.
  unfold lca_bincoprod_inl.
  calc_beta.
Qed.

Definition lca_bincoprod_inr
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co (lin_pair · lca_bincoprod_right) • V 0 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_bincoprod_inr_eq
            {A : linear_combinatory_algebra}
            {a₁ a₂ : A}
  : lca_bincoprod_inr · (!a₁) · a₂
    =
    lin_pair · lca_bincoprod_right · a₂.
Proof.
  unfold lca_bincoprod_inr.
  calc_beta.
Qed.

Definition lca_bincoprod_map_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (V 1 • V 3 • V 4 • V 2 • V 0 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl (Λl (Λl t))))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Definition lca_bincoprod_map
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_bincoprod_map_help • V 1 • V 2 • V 3) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl (Λl t)))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_bincoprod_map_eq
            {A : linear_combinatory_algebra}
            {a₁ a₂ a₃ b₁ b₂ : A}
  : lca_bincoprod_map · a₃ · a₁ · a₂ · (lin_pair · b₁ · b₂)
    =
    b₁ · a₁ · a₂ · a₃ · b₂.
Proof.
  unfold lca_bincoprod_map.
  calc_beta.
  rewrite lca_let_combinator_eq.
  unfold lca_bincoprod_map_help.
  calc_beta.
Qed.

Definition lca_eval
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • Co I : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_eval_eq
            {A : linear_combinatory_algebra}
            {a b₁ b₂ : A}
  : lca_eval · (!a) · (lin_pair · b₁ · b₂) = b₁ · b₂.
Proof.
  unfold lca_eval.
  calc_beta.
  rewrite lca_let_combinator_eq.
  rewrite linear_combinatory_algebra_i_eq.
  apply idpath.
Qed.

Definition lca_lam_pt
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (V 3 • V 1 • (Co lin_pair • V 2 • V 0) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λn (Λl t)))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_lam_pt_eq
            {A : linear_combinatory_algebra}
            {a b b' c : A}
  : lca_lam_pt · a · b · (!b') · c = a · (!b') · (lin_pair · b · c).
Proof.
  unfold lca_lam_pt.
  calc_beta.
Qed.

Definition lca_lam
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (V 3 • V 2 • (Co lin_pair • V 1 • V 0) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl (Λl (Λl t)))) _) ;  
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_lam_eq
            {A : linear_combinatory_algebra}
            {a b b' c : A}
  : lca_lam · a · b · b' · c = a · b · (lin_pair · b' · c).
Proof.
  unfold lca_lam.
  calc_beta.
Qed.

Section LinPairPair.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  Definition lin_pair_to_pair_pair
    : A.
  Proof.
    pose (Excl (Co (pair%ca : AC) • V 1 • V 0)) as t.
    simple refine (closed_lin_term_eval (Λn (Λn t)) _) ;  
      unfold t ;
      check_linear_lam.
  Defined.
    
  Definition lin_pair_to_pair
    : A.
  Proof.
    pose (Co lca_let • V 0 • Co lin_pair_to_pair_pair : lin_term A) as t.
    simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;  
      unfold t ;
      check_linear_lam.
  Defined.

  Proposition lin_pair_to_pair_eq
              {a b c : A}
    : lin_pair_to_pair · (!a) · (lin_pair · (!b) · (!c))
      =
      !((pair : AC)%ca · b · c).
  Proof.
    unfold lin_pair_to_pair.
    calc_beta.
    rewrite lca_let_combinator_eq.
    unfold lin_pair_to_pair_pair.
    calc_beta.
  Qed.

  Definition to_lin_pair_proj
    : A.
  Proof.
    pose (Co lin_pair
            • (Excl (Co (π₁ : AC)%ca • V 0))
            • (Excl (Co (π₂ : AC)%ca • V 0))) as t.
    simple refine (closed_lin_term_eval (Λn (Λn t)) _) ;  
      unfold t ;
      check_linear_lam.
  Defined.

  Proposition to_lin_pair_proj_eq
              {a b : A}
    : to_lin_pair_proj · (!a) · (!b)
      =
      lin_pair · (!((π₁ : AC)%ca · b)) · (!((π₂ : AC)%ca · b)).
  Proof.
    unfold to_lin_pair_proj.
    calc_beta.
  Qed.
End LinPairPair.

Definition lca_k_I
           {A : linear_combinatory_algebra}
  : A.
Proof.
  simple refine (closed_lin_term_eval (Λn (Λn (Co I))) _) ;
    check_linear_lam.
Defined.

Proposition lca_k_I_eq
            {A : linear_combinatory_algebra}
            {a b : A}
  : lca_k_I · (!a) · (!b) = I.
Proof.
  unfold lca_k_I.
  calc_beta.
Qed.

Definition lca_lin_lam
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (V 3 • V 0 • V 1 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λn (Λl (Λl t)))) _) ;
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_lin_lam_eq
            {A : linear_combinatory_algebra}
            {a b₁ b₂ c : A}
  : lca_lin_lam · a · (!b₁) · b₂ · c = a · c · b₂.
Proof.
  unfold lca_lin_lam.
  calc_beta.
Qed.

Definition lca_lin_sig_elim
            {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • V 2 : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λn (Λl t))) _) ;
    unfold t ;
    check_linear_lam.
Defined.

Proposition lca_lin_sig_elim_eq
            {A : linear_combinatory_algebra}
            {a b c₁ c₂ : A}
  : lca_lin_sig_elim · a · (!b) · (lin_pair · c₁ · c₂) = a · c₁ · c₂.
Proof.
  unfold lca_lin_sig_elim.
  calc_beta.
  rewrite lca_let_combinator_eq.
  apply idpath.
Qed.

Section BeckChevalley.
  Context {A : linear_combinatory_algebra}.

  Let AC : combinatory_algebra := lca_to_ca A.

  Definition lca_lin_sum_bc_help
    : A.
  Proof.
    pose (Co lin_pair • (Excl (Co (π₁ : AC)%ca • V 1)) • V 0) as t.
    simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;
      unfold t ;
      check_linear_lam.
  Defined.
  
  Definition lca_lin_sum_bc
    : A.
  Proof.
    pose (Co lca_let • V 0 • Co lca_lin_sum_bc_help) as t.
    simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;
      unfold t ;
      check_linear_lam.
  Defined.

  Definition lca_lin_sum_bc_eq
             {a b₁ b₂ : A} 
    : lca_lin_sum_bc · (!a) · (lin_pair · (!b₁) · b₂)
      =
      lin_pair · (!((π₁ : AC)%ca · b₁)) · b₂.
  Proof.
    unfold lca_lin_sum_bc.
    calc_beta.
    rewrite lca_let_combinator_eq.
    unfold lca_lin_sum_bc_help.
    calc_beta.
  Qed.

  Definition lca_lin_sum_bc_inv_help
    : A.
  Proof.
    pose (Co lin_pair • Excl (Co (pair : AC)%ca • V 1 • V 2) • V 0) as t.
    simple refine (closed_lin_term_eval (Λn (Λn (Λl t))) _) ;
      unfold t ;
      check_linear_lam.
  Defined.
    
  Definition lca_lin_sum_bc_inv
    : A.
  Proof.
    pose (Co lca_let • V 0 • (Co lca_lin_sum_bc_inv_help • V 1)) as t.
    simple refine (closed_lin_term_eval (Λl (Λl t)) _) ;
      unfold t ;
      check_linear_lam.
  Defined.

  Proposition lca_lin_sum_bc_inv_eq
              {a b₁ b₂ : A}
    : lca_lin_sum_bc_inv · (!a) · (lin_pair · (! b₁) · b₂)
      =
      lin_pair · (!((pair : AC)%ca · b₁ · a)) · b₂.
  Proof.
    unfold lca_lin_sum_bc_inv.
    calc_beta.
    rewrite lca_let_combinator_eq.
    unfold lca_lin_sum_bc_inv_help.
    calc_beta.
  Qed.
End BeckChevalley.

Definition lca_frobenius_pair
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lin_pair • V 1 • (Co lin_pair • V 2 • V 0) : lin_term A) as t.
    simple refine (closed_lin_term_eval (Λl (Λl (Λl t))) _) ;
      unfold t ;
      check_linear_lam.
Defined.

Definition lca_frobenius_help
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • (Co lca_frobenius_pair • V 1) : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λl (Λl t)) _) ;
    unfold t ;
    check_linear_lam.
Defined.
  
Definition lca_frobenius
           {A : linear_combinatory_algebra}
  : A.
Proof.
  pose (Co lca_let • V 0 • Co lca_frobenius_help : lin_term A) as t.
  simple refine (closed_lin_term_eval (Λn (Λl t)) _) ;
      unfold t ;
      check_linear_lam.
Defined.

Proposition lca_frobenius_eq
            {A : linear_combinatory_algebra}
            {a b c₁ c₂ : A}
  : lca_frobenius · (!a) · (lin_pair · b · (lin_pair · c₁ · c₂))
    =
    lin_pair · c₁ · (lin_pair · b · c₂).
Proof.
  unfold lca_frobenius.
  calc_beta.
  rewrite lca_let_combinator_eq.
  unfold lca_frobenius_help.
  calc_beta.
  rewrite lca_let_combinator_eq.
  unfold lca_frobenius_pair.
  calc_beta.
Qed.
