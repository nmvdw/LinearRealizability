(**

 Completeness for linear combinatory algebra

 Combinatory completeness for linear combinatory algebras comes in two version.
 - Linear λ-abstraction
 - Non-linear λ-abstraction
 Linear λ-abstraction is only possible if the variable occurs linear in the term. Non-linear
 λ-abstract is always possible, but it only β-reduces on terms of the shape `! a`. Every
 linear combinatory algebra supports both versions of λ-abstraction.

 Contents
 1. Terms in a linear combinatory algebra
 2. Linear variables
 3. Well-scopedness of variables
 4. Substitution
 5. Lemmas for substitution
 6. Evaluation and λ-abstraction
 7. Well-scopedness of λ-abstraction
 8. β-rules
 9. Substitution on λ-abstraction
 10. Nonlinear λ-abstraction
 11. β-rule and substitution equation
 12. Tactics for linear completenenss

 *)
Require Import UniMath.MoreFoundations.All.

Require Import NatOrder.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.LinearCombinatoryAlgebra.

Local Open Scope lca.

(** * 1. Terms in a linear combinatory algebra *)
Inductive lin_term (A : linear_combinatory_algebra) : UU :=
| Var : ℕ → lin_term A
| Const : A → lin_term A
| Excl : lin_term A → lin_term A
| App : lin_term A → lin_term A → lin_term A.

Arguments Var {A} n.
Arguments Const {A} a.
Arguments Excl {A} t.
Arguments App {A} t₁ t₂.

Notation "'V'" := Var : lca.
Notation "'Co'" := Const : lca.

Notation "t₁ • t₂" := (App t₁ t₂) (at level 40, left associativity) : lca. (* \bu 2 *)

(** * 2. Linear variables *)
Definition does_not_occur
           {A : linear_combinatory_algebra}
           (t : lin_term A)
           (n : ℕ)
  : UU.
Proof.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ].
  - exact (¬(m = n)).
  - exact unit.
  - exact IHt.
  - exact (IHt₁ × IHt₂).
Defined.

Proposition does_not_occur_var
            {A : linear_combinatory_algebra}
            {m n : ℕ}
            (p : m ≠ n)
  : @does_not_occur A (V m) n.
Proof.
  apply nat_neq_to_nopath.
  exact p.
Qed.

Proposition does_not_occur_excl
            {A : linear_combinatory_algebra}
            {t : lin_term A}
            {n : ℕ}
            (H : does_not_occur t n)
  : does_not_occur (Excl t) n.
Proof.
  exact H.
Qed.

Proposition does_not_occur_app
            {A : linear_combinatory_algebra}
            {t₁ t₂ : lin_term A}
            {n : ℕ}
            (H₁ : does_not_occur t₁ n)
            (H₂ : does_not_occur t₂ n)
  : does_not_occur (t₁ • t₂) n.
Proof.
  exact (H₁ ,, H₂).
Qed.
            
Definition occurs_lineary
           {A : linear_combinatory_algebra}
           (t : lin_term A)
           (n : ℕ)
  : UU.
Proof.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ].
  - exact (m = n).
  - exact ∅.
  - exact ∅.
  - exact ((IHt₁ × does_not_occur t₂ n) ⨿ (does_not_occur t₁ n × IHt₂)).
Defined.

Proposition occurs_lineary_var
            {A : linear_combinatory_algebra}
            (m n : ℕ)
            (p : m = n)
  : @occurs_lineary A (V m) n.
Proof.
  cbn.
  exact p.
Qed.

Proposition occurs_lineary_left
            {A : linear_combinatory_algebra}
            {t₁ t₂ : lin_term A}
            (n : ℕ)
            (H₁ : occurs_lineary t₁ n)
            (H₂ : does_not_occur t₂ n)
  : occurs_lineary (t₁ • t₂) n.
Proof.
  exact (inl (H₁ ,, H₂)).
Qed.

Proposition occurs_lineary_right
            {A : linear_combinatory_algebra}
            {t₁ t₂ : lin_term A}
            (n : ℕ)
            (H₁ : does_not_occur t₁ n)
            (H₂ : occurs_lineary t₂ n)
  : occurs_lineary (t₁ • t₂) n.
Proof.
  exact (inr (H₁ ,, H₂)).
Qed.

(** * 3. Well-scopedness of variables *)
Definition is_well_scoped_lin_term
           {A : linear_combinatory_algebra}
           (t : lin_term A)
           (n : ℕ)
  : hProp.
Proof.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ].
  - exact (m < n).
  - exact htrue.
  - exact IHt.
  - exact (IHt₁ ∧ IHt₂).
Defined.

(** * 4. Substitution *)

(**
   The variable `m` gets replaced by `c`.
   Variables larger than `m`: decremented by 1
   Variables lower than `m`: stay the same

   The intuition is that `m` gets removed from the scope, so the variables larger than it
   become one closer to their corresponding lambda. That's why the variables larger than `m`
   get decremented by 1, and why the others stay the same.
 *)
Definition var_subst
           {A : linear_combinatory_algebra}
           (n : ℕ)
           (c : A)
           (m : ℕ)
  : lin_term A.
Proof.
  destruct (natgthorleh n m) as [ p | p ].
  - destruct n as [ | n ].
    + apply fromempty.
      apply nopathsfalsetotrue.
      exact p.
    + exact (Var n).
  - destruct (natlehchoice _ _ p) as [ q | q ].
    + exact (Var n).
    + exact (Co c).
Defined.

Definition lin_term_subst
           {A : linear_combinatory_algebra}
           (t : lin_term A)
           (m : ℕ)
           (c : A)
  : lin_term A.
Proof.
  induction t as [ n | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ].
  - exact (var_subst n c m).
  - exact (Co ca).
  - exact (Excl IHt).
  - exact (IHt₁ • IHt₂).
Defined.

Notation "t '{{' m ↦ c '}}'" := (lin_term_subst t m c) : lca.

(** * 5. Lemmas for substitution *)
Proposition is_well_scoped_var_subst
            {A : linear_combinatory_algebra}
            {k n : ℕ}
            (a : A)
            (m : ℕ)
            (p : k < 1 + n)
            (q : m ≤ n)
  : is_well_scoped_lin_term (var_subst k a m) n.
Proof.
  unfold var_subst.
  destruct (natgthorleh k m) as [ r | r ].
  - destruct k as [ | k ].
    + apply fromempty.
      apply nopathsfalsetotrue.
      exact r.
    + simpl.
      apply p.
  - destruct (natlehchoice _ _ r) as [ r' | r' ].
    + exact (natlthlehtrans _ _ _ r' q).
    + exact tt.
Qed.

Proposition is_well_scoped_lin_tm_subst
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            {n : ℕ}
            (Ht : is_well_scoped_lin_term t (1 + n))
            (a : A)
            (m : ℕ)
            (p : m ≤ n)
  : is_well_scoped_lin_term (t {{ m ↦ a }}) n.
Proof.
  induction t as [ k | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ].
  - use is_well_scoped_var_subst.
    + apply Ht.
    + exact p.
  - exact tt.
  - simpl.
    apply IHt.
    exact Ht.
  - split.
    + apply IHt₁.
      apply Ht.
    + apply IHt₂.
      apply Ht.
Qed.

Proposition does_not_occur_var_subst
            {A : linear_combinatory_algebra}
            {m k : ℕ}
            (H : m != 0)
            (c : A)
  : does_not_occur (var_subst m c (1 + k)) 0.
Proof.
  unfold var_subst.
  destruct (natgthorleh m (1 + k)) as [ p | p ].
  - destruct m as [ | m ].
    + apply fromempty.
      apply nopathsfalsetotrue.
      exact p.
    + cbn.
      pose (natgthandpluslinv _ _ 1 p) as r.
      pose (natgthgehtrans _ _ _ r (natgehn0 k)) as r'.
      intro s.
      rewrite s in r'.
      apply (negnatgth0n _ r').
  - destruct (natlehchoice _ _ p) as [ q | q ].
    + exact H.
    + exact tt.
Qed.

Proposition does_not_occur_subst
            {A : linear_combinatory_algebra}
            {t : lin_term A}
            (H : does_not_occur t 0)
            (c : A)
            (k : ℕ)
  : does_not_occur (t {{ 1 + k ↦ c }}) 0.
Proof.
  revert H c.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H c.
  - apply does_not_occur_var_subst.
    exact H.
  - exact tt.
  - apply IHt.
    exact H.
  - split.
    + apply IHt₁.
      exact (pr1 H).
    + apply IHt₂.
      exact (pr2 H).
Defined.

Proposition occurs_lineary_subst
            {A : linear_combinatory_algebra}
            {t : lin_term A}
            (H : occurs_lineary t 0)
            (c : A)
            (k : ℕ)
  : occurs_lineary (t {{ 1 + k ↦ c }}) 0.
Proof.
  revert H c.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H c.
  - abstract
      (simpl in H ;
       rewrite H ;
       simpl ;
       apply idpath).
  - simpl in *.
    exact H.
  - simpl in *.
    exact H.
  - destruct H as [ H | H ].
    + simpl.
      use inl.
      split.
      * apply IHt₁.
        exact (pr1 H).
      * apply does_not_occur_subst.
        exact (pr2 H).
    + simpl.
      use inr.
      split.
      * apply does_not_occur_subst.
        exact (pr1 H).
      * apply IHt₂.
        exact (pr2 H).
Defined.

(** * 6. Evaluation and λ-abstraction *)
Definition closed_lin_term_eval
           {A : linear_combinatory_algebra}
           (t : lin_term A)
           (Ht : is_well_scoped_lin_term t 0)
  : A.
Proof.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ].
  - use fromempty.
    use nopathsfalsetotrue.
    exact Ht.
  - exact ca.
  - exact (!(IHt Ht)).
  - exact (IHt₁ (pr1 Ht) · IHt₂ (pr2 Ht)).
Defined.

Notation "'ev' t" := (closed_lin_term_eval t _) (at level 200, only printing) : lca.

Proposition closed_lin_term_eval_eq
            {A : linear_combinatory_algebra}
            {t t' : lin_term A}
            (p : t = t')
            (Ht : is_well_scoped_lin_term t 0)
  : closed_lin_term_eval t Ht
    =
    closed_lin_term_eval t' (transportf (λ t, is_well_scoped_lin_term t 0) p Ht).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Definition lam_lin_term_does_not_occur
           {A : linear_combinatory_algebra}
           (t : lin_term A)
           (H : does_not_occur t 0)
  : lin_term A.
Proof.
  revert H.
  induction t as [ n | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; simpl.
  - destruct n as [ | n ].
    + intro q.
      apply fromempty.
      apply q.
      apply idpath.
    + intro.
      exact (V n).
  - intro q.
    exact (Co ca).
  - intro p.
    refine (Excl _).
    exact (IHt p).
  - intro pq.
    exact (IHt₁ (pr1 pq) • IHt₂ (pr2 pq)).
Defined.

Proposition lam_lin_term_does_not_occur_eq
            {A : linear_combinatory_algebra}
            {t t' : lin_term A}
            (p : t = t')
            (H : does_not_occur t 0)
  : lam_lin_term_does_not_occur t H
    =
    lam_lin_term_does_not_occur t' (transportf (λ z, does_not_occur z 0) p H).
Proof.
  induction p.
  apply idpath.
Qed.

Definition lam_lin_term_linear
           {A : linear_combinatory_algebra}
           (t : lin_term A)
           (H : occurs_lineary t 0)
  : lin_term A.
Proof.
  revert H.
  induction t as [ n | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; simpl.
  - intro p.
    exact (Co I).
  - exact fromempty.
  - apply fromempty.
  - intros pq.
    induction pq as [ pq | pq ].
    + exact (Co C • IHt₁ (pr1 pq) • lam_lin_term_does_not_occur t₂ (pr2 pq)).
    + exact (Co B • lam_lin_term_does_not_occur t₁ (pr1 pq) • IHt₂ (pr2 pq)).
Defined.

Notation "'Λl' t" := (lam_lin_term_linear t _) (at level 200).

Proposition lam_lin_term_linear_eq
            {A : linear_combinatory_algebra}
            {t t' : lin_term A}
            (p : t = t')
            (H : occurs_lineary t 0)
  : lam_lin_term_linear t H
    =
    lam_lin_term_linear t' (transportf (λ t, occurs_lineary t 0) p H).
Proof.
  induction p.
  apply idpath.
Qed.

(** * 7. Well-scopedness of λ-abstraction *)
Proposition lam_lin_term_does_not_occur_well_scoped
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : does_not_occur t 0)
            {n : ℕ}
            (Hn : is_well_scoped_lin_term t (1 + n))
  : is_well_scoped_lin_term
      (lam_lin_term_does_not_occur t H)
      n.
Proof.
  revert H n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H n Hn.
  - destruct m as [ | m ].
    + apply fromempty.
      apply H.
      apply idpath.
    + exact Hn.
  - exact tt.
  - apply IHt.
    apply Hn.
  - split.
    + apply IHt₁.
      exact (pr1 Hn).
    + apply IHt₂.
      exact (pr2 Hn).
Qed.
    
Proposition lam_lin_term_linear_well_scoped
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : occurs_lineary t 0)
            {n : ℕ}
            (Hn : is_well_scoped_lin_term t (1 + n))
  : is_well_scoped_lin_term
      (lam_lin_term_linear t H)
      n.
Proof.
  revert H n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H n Hn.
  - exact tt.
  - apply fromempty.
    exact H.
  - apply fromempty.
    exact H.
  - induction H as [ H | H ].
    + split.
      * simpl.
        refine (tt ,, _).
        apply IHt₁.
        exact (pr1 Hn).
      * apply lam_lin_term_does_not_occur_well_scoped.
        exact (pr2 Hn).
    + split.
      * simpl.
        refine (tt ,, _).
        apply lam_lin_term_does_not_occur_well_scoped.
        exact (pr1 Hn).
      * apply IHt₂.
        exact (pr2 Hn).
Qed.

Proposition lam_lin_term_does_not_occur_not_occur
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : does_not_occur t 0)
            {n : ℕ}
            (Hn : does_not_occur t (1 + n))
  : does_not_occur (lam_lin_term_does_not_occur t H) n.
Proof.
  revert H n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H n Hn.
  - simpl in H, Hn.
    destruct m as [ | m ] ; simpl.
    + apply fromempty.
      apply H.
      apply idpath.
    + intro p.
      apply Hn.
      rewrite p.
      apply idpath.
  - exact Hn.
  - simpl in *.
    apply IHt.
    exact Hn.
  - split ; simpl in *.
    + apply IHt₁.
      apply Hn.
    + apply IHt₂.
      apply Hn.
Qed.

Proposition lam_lin_term_does_not_occur_lineary
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : does_not_occur t 0)
            {n : ℕ}
            (Hn : occurs_lineary t (1 + n))
  : occurs_lineary (lam_lin_term_does_not_occur t H) n.
Proof.
  revert H n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H n Hn.
  - simpl in H, Hn.
    destruct m as [ | m ].
    + apply fromempty.
      apply H.
      apply idpath.
    + apply invmaponpathsS.
      exact Hn.
  - exact Hn.
  - exact Hn.
  - induction Hn as [ Hn | Hn ] ; simpl.
    + use inl.
      split.
      * apply IHt₁.
        apply Hn.
      * apply lam_lin_term_does_not_occur_not_occur.
        apply Hn.
    + use inr.
      split.
      * apply lam_lin_term_does_not_occur_not_occur.
        apply Hn.
      * apply IHt₂.
        apply Hn.
Qed.

Proposition lam_lin_term_var_does_not_occur
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : occurs_lineary t 0)
            {n : ℕ}
            (Hn : does_not_occur t (1 + n))
  : does_not_occur (lam_lin_term_linear t H) n.
Proof.
  revert H n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H n Hn.
  - exact tt.
  - apply fromempty.
    exact H.
  - apply fromempty.
    exact H.
  - induction H as [ H | H ] ; simpl ; repeat split.
    + apply IHt₁.
      apply Hn.
    + apply lam_lin_term_does_not_occur_not_occur.
      apply Hn.
    + apply lam_lin_term_does_not_occur_not_occur.
      apply Hn.
    + apply IHt₂.
      apply Hn.
Qed.

Proposition lam_lin_term_occurs_lineary
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : occurs_lineary t 0)
            {n : ℕ}
            (Hn : occurs_lineary t (1 + n))
  : occurs_lineary (lam_lin_term_linear t H) n.
Proof.
  revert H n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H n Hn.
  - simpl ; simpl in Hn, H.
    rewrite H in Hn.
    exact (negpaths0sx _ Hn).
  - apply fromempty.
    exact H.
  - apply fromempty.
    exact H.
  - induction H as [ H | H ], Hn as [ Hn | Hn ] ; simpl.
    + use inl.
      split.
      * use inr.
        refine (tt ,, _).
        apply IHt₁.
        exact (pr1 Hn).
      * apply lam_lin_term_does_not_occur_not_occur.
        apply Hn.
    + use inr.
      split.
      * refine (tt ,, _).
        apply lam_lin_term_var_does_not_occur.
        apply Hn.
      * apply lam_lin_term_does_not_occur_lineary.
        apply Hn.
    + use inl.
      split.
      * use inr.
        refine (tt ,, _).
        apply lam_lin_term_does_not_occur_lineary.
        apply Hn.
      * apply lam_lin_term_var_does_not_occur.
        apply Hn.
    + use inr.
      split.
      * refine (tt ,, _).
        apply lam_lin_term_does_not_occur_not_occur.
        apply Hn.
      * apply IHt₂.
        apply Hn.
Qed.

(** * 8. β-rules *)
Proposition lam_lin_term_beta_does_not_occur
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : does_not_occur t 0)
            (c : A)
            (Hn : is_well_scoped_lin_term t 1)
  : closed_lin_term_eval
      (lam_lin_term_does_not_occur t H)
      (lam_lin_term_does_not_occur_well_scoped _ H Hn)
    =
    closed_lin_term_eval
      (t {{ 0 ↦ c }})
      (is_well_scoped_lin_tm_subst _ Hn _ _ (isreflnatleh 0)).
Proof.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ].
  - destruct m as [ | m ].
    + apply fromempty.
      apply H.
      apply idpath.
    + apply fromempty.
      simpl in *.
      apply nopathsfalsetotrue.
      exact Hn.
  - cbn.
    apply idpath.
  - simpl.
    refine (pathsinv0 _).
    etrans.
    {
      apply maponpaths.
      apply pathsinv0.
      specialize (IHt H Hn).
      refine (IHt @ _).
      apply maponpaths.
      apply propproperty.
    }
    do 2 apply maponpaths.
    apply propproperty.
  - simpl.
    etrans.
    {
      apply maponpaths_2.
      refine (_ @ IHt₁ (pr1 H) (pr1 Hn)).
      apply maponpaths.
      apply propproperty.
    }
    etrans.
    {
      apply maponpaths.
      refine (_ @ IHt₂ (pr2 H) (pr2 Hn)).
      apply maponpaths.
      apply propproperty.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply propproperty.
    }
    apply maponpaths_2.
    apply maponpaths.
    apply propproperty.
Qed.

Proposition lam_lin_term_beta
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : occurs_lineary t 0)
            (c : A)
            (Hn : is_well_scoped_lin_term t 1)
  : closed_lin_term_eval
      (lam_lin_term_linear t H)
      (lam_lin_term_linear_well_scoped t H Hn)
    · c
    =
    closed_lin_term_eval
      (t {{ 0 ↦ c }})
      (is_well_scoped_lin_tm_subst _ Hn _ _ (isreflnatleh _)).
Proof.
  revert H c Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H c Hn.
  - destruct m as [ | m ].
    + simpl.
      rewrite linear_combinatory_algebra_i_eq.
      apply idpath.
    + apply fromempty.
      simpl in *.
      apply nopathsfalsetotrue.
      exact Hn.
  - apply fromempty ; simpl in H.
    exact H.
  - simpl.
    apply fromempty.
    exact H.
  - destruct H as [ H | H ].
    + simpl.
      rewrite linear_combinatory_algebra_c_eq.
      etrans.
      {
        apply maponpaths_2.
        refine (_ @ IHt₁ (pr1 H) c (pr1 Hn)).
        apply maponpaths_2.
        apply maponpaths.
        apply propproperty.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply propproperty.
      }
      apply maponpaths.
      refine (_ @ lam_lin_term_beta_does_not_occur t₂ (pr2 H) c (pr2 Hn) @ _).
      * apply maponpaths.
        apply propproperty.
      * apply maponpaths.
        apply propproperty.
    + simpl.
      rewrite linear_combinatory_algebra_b_eq.
      etrans.
      {
        apply maponpaths.
        refine (_ @ IHt₂ (pr2 H) c (pr2 Hn)).
        apply maponpaths_2.
        apply maponpaths.
        apply propproperty.
      }
      simpl.
      etrans.
      {
        do 2 apply maponpaths.
        apply propproperty.
      }
      apply maponpaths_2.
      refine (_ @ lam_lin_term_beta_does_not_occur t₁ (pr1 H) c (pr1 Hn) @ _).
      * apply maponpaths.
        apply propproperty.
      * apply maponpaths.
        apply propproperty.
Qed.

Proposition from_well_scoped_lam_term_does_not_occur
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : does_not_occur t 0)
            (H' : is_well_scoped_lin_term (lam_lin_term_does_not_occur t H) 0)
  : is_well_scoped_lin_term t 1.
Proof.
  revert H H'.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H H'.
  - destruct m ; simpl in *.
    + apply idpath.
    + exact H'.
  - simpl.
    exact tt.
  - exact (IHt H H').
  - split.
    + exact (IHt₁ (pr1 H) (pr1 H')).
    + exact (IHt₂ (pr2 H) (pr2 H')).
Qed.

Proposition from_well_scoped_lam_term_linear
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : occurs_lineary t 0)
            (H' : is_well_scoped_lin_term (lam_lin_term_linear t H) 0)
  : is_well_scoped_lin_term t 1.
Proof.
  revert H H'.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H H'.
  - simpl in H.
    rewrite H ; simpl.
    apply idpath.
  - simpl.
    exact tt.
  - simpl in H.
    apply fromempty.
    exact H.
  - destruct H as [ H | H ].
    + split.
      * apply (IHt₁ (pr1 H)).
        apply H'.
      * apply (from_well_scoped_lam_term_does_not_occur _ (pr2 H)).
        apply H'.
    + split.
      * apply (from_well_scoped_lam_term_does_not_occur _ (pr1 H)).
        apply H'.
      * apply (IHt₂ (pr2 H)).
        apply H'.
Qed.

Proposition lam_lin_term_beta'
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : occurs_lineary t 0)
            (c : A)
            (H' : is_well_scoped_lin_term (Λl t) 0)
            (Hn := from_well_scoped_lam_term_linear t H H')
  : closed_lin_term_eval
      (lam_lin_term_linear t H)
      H'
    · c
    =
    closed_lin_term_eval
      (t {{ 0 ↦ c }})
      (is_well_scoped_lin_tm_subst _ Hn _ _ (isreflnatleh _)).
Proof.  
  refine (_ @ lam_lin_term_beta t H c Hn).
  apply maponpaths_2.
  apply maponpaths.
  apply propproperty.
Qed.

(** * 9. Substitution on λ-abstraction *)
Proposition lam_does_not_occur_var_subst
            {A : linear_combinatory_algebra}
            (m k : ℕ)
            (c : A)
            (p : 1 + m != 0)
  : var_subst m c k
    =
    lam_lin_term_does_not_occur
      (var_subst (1 + m) c (1 + k))
      (does_not_occur_var_subst p c).
Proof.
  unfold var_subst.
  destruct (natgthorleh m k) as [ q | q ].
  + refine (pathsinv0 _).
    etrans.
    {
      refine (lam_lin_term_does_not_occur_eq _ _).
      simpl.
      pose (natgthorleh_left (natgthandplusl _ _ 1 q)) as r.
      simpl in r.
      rewrite r.
      apply idpath.
    }
    simpl.
    destruct m as [ | m ].
    * apply fromempty.
      use nopathsfalsetotrue.
      exact q.
    * apply idpath.
  + refine (pathsinv0 _).
    etrans.
    {
      refine (lam_lin_term_does_not_occur_eq _ _).
      simpl.
      pose (natgthorleh_right (natgthandplusl _ _ 1 q)) as r.
      simpl in r.
      rewrite r.
      apply idpath.
    }
    destruct (natlehchoice m k q) as [ r | r ].
    * etrans.
      {
        refine (lam_lin_term_does_not_occur_eq _ _).
        pose (@natlehchoice_left (1 + m) (1 + k) q (natlthandplusl _ _ 1 r)) as r'.
        simpl in r'.
        rewrite r'.
        apply idpath.
      }
      simpl.
      apply idpath.        
    * induction r.
      etrans.
      {
        refine (lam_lin_term_does_not_occur_eq _ _).
        pose (@natlehchoice_right (1 + m) (1 + m) q (idpath _)) as r'.
        simpl in r'.
        rewrite r'.
        apply idpath.
      }
      simpl.
      apply idpath.
Qed.

Proposition lam_lin_term_does_not_occur_subst
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : does_not_occur t 0)
            (c : A)
            (k : ℕ)
  : (lam_lin_term_does_not_occur t H) {{ k ↦ c }}
    =
    lam_lin_term_does_not_occur
      (t {{ 1 + k ↦ c }})
      (does_not_occur_subst H _ _).
Proof.
  revert c.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros c.
  - cbn -[lam_lin_term_does_not_occur].
    destruct m as [ | m ].
    + simpl.
      apply fromempty.
      apply H.
      apply idpath.
    + simpl.
      apply lam_does_not_occur_var_subst.
  - simpl.
    apply idpath.
  - simpl.
    apply maponpaths.
    exact (IHt H c).
  - simpl.
    rewrite (IHt₁ (pr1 H) c).
    rewrite (IHt₂ (pr2 H) c).    
    apply idpath.
Qed.

Proposition lam_lin_term_linear_subst
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : occurs_lineary t 0)
            (c : A)
            (k : ℕ)
  : (lam_lin_term_linear t H) {{ k ↦ c }}
    =
    (lam_lin_term_linear (t {{ 1 + k ↦ c }}) (occurs_lineary_subst H _ _)).
Proof.
  revert c.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros c.
  - destruct m as [ | m ].
    + simpl in *.
      apply idpath.
    + simpl in H.
      apply fromempty.
      exact (negpathssx0 m H).
  - simpl in H.
    apply fromempty.
    exact H.
  - simpl in H.
    apply fromempty.
    exact H.
  - destruct H as [ H | H ].
    + simpl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (IHt₁ (pr1 H) c).
      }
      rewrite lam_lin_term_does_not_occur_subst.
      apply idpath.
    + simpl.
      etrans.
      {
        apply maponpaths.
        exact (IHt₂ (pr2 H) c).
      }
      apply maponpaths_2.
      apply maponpaths.
      apply lam_lin_term_does_not_occur_subst.
Qed.

(** * 10. Nonlinear λ-abstraction *)
Definition lam_lin_term_nonlinear
           {A : linear_combinatory_algebra}
           (t : lin_term A)
  : lin_term A.
Proof.
  induction t as [ n | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; simpl.
  - destruct n as [ | n ].
    + exact (Co I).
    + exact (Co K • (V n)).
  - (**
       Note that we do not pick `Co (K · ca)` here.
       This guarantees that we can prove the substitution equation below. 
     *)
    exact (Co K • Co ca).
  - exact (Co B • (Co F • Excl IHt) • Co δ).
  - exact (Co S • IHt₁ • IHt₂).
Defined.

Notation "'Λn' t" := (lam_lin_term_nonlinear t) (at level 200).

Proposition lam_lin_term_nonlinear_well_scoped
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            {n : ℕ}
            (Hn : is_well_scoped_lin_term t (1 + n))
  : is_well_scoped_lin_term
      (lam_lin_term_nonlinear t)
      n.
Proof.
  revert n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros n Hn.
  - destruct m as [ | m ].
    + exact tt.
    + refine (tt ,, _).
      exact Hn.
  - exact (tt ,, tt).
  - simpl.
    refine ((tt ,, tt ,, _) ,, tt).
    apply IHt.
    apply Hn.
  - split.
    + refine (tt ,, _).
      apply IHt₁.
      exact (pr1 Hn).
    + apply IHt₂.
      exact (pr2 Hn).
Qed.

Proposition lam_lin_term_nonlinear_not_occur
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            {n : ℕ}
            (Hn : does_not_occur t (1 + n))
  : does_not_occur (lam_lin_term_nonlinear t) n.
Proof.
  revert n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros n Hn.
  - simpl in Hn.
    destruct m as [ | m ] ; simpl.
    + exact tt.
    + refine (tt ,, _).
      intro p.
      apply Hn.
      rewrite p.
      apply idpath.
  - exact (tt ,, tt).
  - simpl in *.
    refine ((tt ,, tt ,, _) ,, tt).
    apply IHt.
    exact Hn.
  - split ; simpl in *.
    + refine (tt ,, _).
      apply IHt₁.
      apply Hn.
    + apply IHt₂.
      apply Hn.
Qed.

Proposition lam_lin_term_nonlinear_lineary
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            {n : ℕ}
            (Hn : occurs_lineary t (1 + n))
  : occurs_lineary (lam_lin_term_nonlinear t) n.
Proof.
  revert n Hn.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros n Hn.
  - simpl in Hn.
    destruct m as [ | m ].
    + apply fromempty.
      exact (negpaths0sx _ Hn).
    + simpl.
      use inr.
      refine (tt ,, _).
      apply invmaponpathsS.
      exact Hn.
  - apply fromempty.
    exact Hn.
  - apply fromempty.
    exact Hn.
  - induction Hn as [ Hn | Hn ] ; simpl.
    + use inl.
      split.
      * use inr.
        refine (tt ,, _).
        apply IHt₁.
        apply Hn.
      * apply lam_lin_term_nonlinear_not_occur.
        apply Hn.
    + use inr.
      split.
      * refine (tt ,, _).
        apply lam_lin_term_nonlinear_not_occur.
        apply Hn.
      * apply IHt₂.
        apply Hn.
Qed.

(** * 11. β-rule and substitution equation *)
Proposition lam_lin_term_nonlinear_beta
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (c : A)
            (Ht : is_well_scoped_lin_term t 1)
  : closed_lin_term_eval
      (lam_lin_term_nonlinear t)
      (lam_lin_term_nonlinear_well_scoped t Ht)
    · (! c)
    =
    closed_lin_term_eval
      (t {{ 0 ↦ ! c }})
      (is_well_scoped_lin_tm_subst _ Ht _ _ (isreflnatleh 0)).
Proof.
  revert Ht.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros Ht.
  - destruct m as [ | m ] ; simpl.
    + rewrite linear_combinatory_algebra_i_eq.
      apply idpath.
    + apply fromempty.
      apply nopathsfalsetotrue.
      exact Ht.
  - simpl.
    rewrite linear_combinatory_algebra_k_eq.
    apply idpath.
  - simpl.
    rewrite linear_combinatory_algebra_b_eq.
    rewrite linear_combinatory_algebra_delta_eq.
    rewrite linear_combinatory_algebra_f_eq.
    apply maponpaths.
    refine (_ @ IHt Ht @ _).
    + apply maponpaths_2.
      apply maponpaths.
      apply propproperty.
    + apply maponpaths.
      apply propproperty.
  - simpl.
    rewrite linear_combinatory_algebra_s_eq.
    etrans.
    {
      apply maponpaths.
      refine (_ @ IHt₂ (pr2 Ht)).
      apply maponpaths_2.
      apply maponpaths.
      apply propproperty.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (_ @ IHt₁ (pr1 Ht)).
      apply maponpaths_2.
      apply maponpaths.
      apply propproperty.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply propproperty.
    }
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply propproperty.
    }
    apply idpath.
Qed.

Proposition from_well_scoped_lam_term_nonlinear
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (H : is_well_scoped_lin_term (Λn t) 0)
  : is_well_scoped_lin_term t 1.
Proof.
  revert H.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros H.
  - destruct m ; simpl in *.
    + apply idpath.
    + apply H.
  - simpl.
    exact tt.
  - apply IHt.
    apply H.
  - split.
    + apply IHt₁.
      apply H.
    + apply IHt₂.
      apply H.
Qed.

Proposition lam_lin_term_nonlinear_beta'
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (c : A)
            (H : is_well_scoped_lin_term (Λn t) 0)
            (Ht := from_well_scoped_lam_term_nonlinear t H)
  : closed_lin_term_eval
      (lam_lin_term_nonlinear t)
      H
    · (! c)
    =
    closed_lin_term_eval
      (t {{ 0 ↦ ! c }})
      (is_well_scoped_lin_tm_subst _ Ht _ _ (isreflnatleh 0)).
Proof.
  refine (_ @ lam_lin_term_nonlinear_beta t c Ht).
  apply maponpaths_2.
  apply maponpaths.
  apply propproperty.
Qed.

Proposition lam_nonlinear_var_subst
            {A : linear_combinatory_algebra}
            (m k : ℕ)
            (c : A)
  : Co K • var_subst m c k
    =
    lam_lin_term_nonlinear (var_subst (1 + m) c (1 + k)).
Proof.
  unfold var_subst.
  destruct (natgthorleh m k) as [ q | q ].
  + refine (pathsinv0 _).
    simpl.
    pose (natgthorleh_left (natgthandplusl _ _ 1 q)) as r.
    simpl in r.
    rewrite r ; clear r.
    simpl.
    destruct m as [ | m ].
    * apply fromempty.
      use nopathsfalsetotrue.
      exact q.
    * apply idpath.
  + simpl.
    pose (natgthorleh_right (natgthandplusl _ _ 1 q)) as r.
    simpl in r.
    rewrite r ; clear r.
    destruct (natlehchoice m k q) as [ r | r ].
    * pose (@natlehchoice_left (1 + m) (1 + k) q (natlthandplusl _ _ 1 r)) as r'.
      simpl in r'.
      rewrite r'.
      simpl.
      apply idpath.
    * induction r.
      pose (@natlehchoice_right (1 + m) (1 + m) q (idpath _)) as r'.
      simpl in r'.
      rewrite r'.
      simpl.
      apply idpath.
Qed.

Proposition lam_lin_term_nonlinear_subst
            {A : linear_combinatory_algebra}
            (t : lin_term A)
            (c : A)
            (k : ℕ)
  : (lam_lin_term_nonlinear t) {{ k ↦ c }}
    =
    lam_lin_term_nonlinear (t {{ 1 + k ↦ c }}).
Proof.
  revert c.
  induction t as [ m | ca | t IHt | t₁ IHt₁ t₂ IHt₂ ] ; intros c.
  - destruct m as [ | m ].
    + simpl in *.
      apply idpath.
    + simpl.
      apply lam_nonlinear_var_subst.
  - simpl.
    apply idpath.
  - simpl.
    rewrite (IHt c).
    apply idpath.
  - simpl.
    rewrite (IHt₁ c), (IHt₂ c).
    apply idpath.
Qed.

(** * 12. Tactics for linear completenenss *)
#[global] Opaque lam_lin_term_linear.
#[global] Opaque lam_lin_term_nonlinear.

Ltac check_well_scoped :=
  match goal with
  | [ |- hProptoType (is_well_scoped_lin_term (Λl _) _) ] =>
      apply lam_lin_term_linear_well_scoped ; check_well_scoped
  | [ |- hProptoType (is_well_scoped_lin_term (Λn _) _) ] =>
      apply lam_lin_term_nonlinear_well_scoped ; check_well_scoped
  | _ => try (repeat split)
  end.

Ltac check_does_not_occur :=
  match goal with
  | [ |- does_not_occur (V _) _ ] => apply does_not_occur_var ; apply tt
  | [ |- does_not_occur (Co _) _ ] => apply tt
  | [ |- does_not_occur (Excl _) _ ] => apply does_not_occur_excl ; check_does_not_occur
  | [ |- does_not_occur (_ • _ ) _ ] => apply does_not_occur_app ; check_does_not_occur
  end.

Ltac check_occurs_lineary :=
  match goal with
  | [ |- occurs_lineary (V _) _ ] => apply occurs_lineary_var ; apply idpath
  | [ |- occurs_lineary (_ • _ ) _ ] =>
      try (apply occurs_lineary_left ; [ check_occurs_lineary | check_does_not_occur ]) ;
      try (apply occurs_lineary_right ; [ check_does_not_occur | check_occurs_lineary ])
  | [ |- occurs_lineary (Λl _) _ ] =>
      apply lam_lin_term_occurs_lineary ; check_occurs_lineary
  | [ |- occurs_lineary (Λn _) _ ] =>
      apply lam_lin_term_nonlinear_lineary ; check_occurs_lineary
  end.

Ltac check_linear_lam :=
  match goal with
  | [ |- occurs_lineary _ _ ] =>
      abstract (check_occurs_lineary)
  | [ |- hProptoType (is_well_scoped_lin_term _ _) ] =>
      abstract (check_well_scoped)
  end.
