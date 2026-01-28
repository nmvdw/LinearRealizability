(**

 Families of sets

 In this file, we construct various operations on families of sets.

 Contents
 1. Dependent sums of families of sets
 2. Dependent products of families of sets
 3. Sections of families

 *)
Require Import UniMath.MoreFoundations.All.

(** * 1. Dependent sums of families of sets *)
Definition dep_sum_set_fam
           {X₁ X₂ : hSet}
           (s : X₁ → X₂)
           (Y : X₁ → hSet)
           (y : X₂)
  : hSet.
Proof.
  refine (∑ (x : X₁), Y x × _)%set.
  use (make_hSet (s x = y)).
  abstract
    (apply isasetaprop ;
     apply setproperty).
Defined.

Definition make_dep_sum_set_fam
           {X₁ X₂ : hSet}
           {s : X₁ → X₂}
           {Y : X₁ → hSet}
           {y : X₂}
           (x : X₁)
           (xx : Y x)
           (p : s x = y)
  : dep_sum_set_fam s Y y
  := x ,, xx ,, p.

Arguments make_dep_sum_set_fam /.

Definition dep_sum_set_fam_fib
           {X₁ X₂ : hSet}
           {s : X₁ → X₂}
           {Y : X₁ → hSet}
           {y : X₂}
           (xx : dep_sum_set_fam s Y y)
  : X₁
  := pr1 xx.

Definition dep_sum_set_fam_el
           {X₁ X₂ : hSet}
           {s : X₁ → X₂}
           {Y : X₁ → hSet}
           {y : X₂}
           (xx : dep_sum_set_fam s Y y)
  : Y (dep_sum_set_fam_fib xx)
  := pr12 xx.

Definition dep_sum_set_fam_path
           {X₁ X₂ : hSet}
           {s : X₁ → X₂}
           {Y : X₁ → hSet}
           {y : X₂}
           (xx : dep_sum_set_fam s Y y)
  : s (dep_sum_set_fam_fib xx) = y
  := pr22 xx.

Proposition dep_sum_set_fam_eq
            {X₁ X₂ : hSet}
            {s : X₁ → X₂}
            {Y : X₁ → hSet}
            {y : X₂}
            {xx₁ xx₂ : dep_sum_set_fam s Y y}
            (p : dep_sum_set_fam_fib xx₁
                 =
                 dep_sum_set_fam_fib xx₂)
            (q : transportf (λ x, Y x) p (dep_sum_set_fam_el xx₁)
                 =
                 dep_sum_set_fam_el xx₂)
  : xx₁ = xx₂.
Proof.
  use total2_paths_f.
  - exact p.
  - use subtypePath.
    {
      intro.
      apply setproperty.
    }
    cbn.
    etrans.
    {
      apply (@pr1_transportf X₁ Y (λ x _, s x = y)).
    }
    exact q.
Qed.

Proposition dep_sum_set_fam_el_transportf_path
            {X₁ X₂ : hSet}
            {s : X₁ → X₂}
            {Y : X₁ → hSet}
            {y₁ y₂ : X₂}
            (p : y₁ = y₂)
            (xx : dep_sum_set_fam s Y y₁)
  : dep_sum_set_fam_fib xx
    =
    dep_sum_set_fam_fib (transportf (dep_sum_set_fam _ _) p xx).
Proof.
  induction p.
  apply idpath.
Defined.
  
Proposition dep_sum_set_fam_el_transportf
            {X₁ X₂ : hSet}
            {s : X₁ → X₂}
            {Y : X₁ → hSet}
            {y₁ y₂ : X₂}
            (p : y₁ = y₂)
            (xx : dep_sum_set_fam s Y y₁)
  : dep_sum_set_fam_el (transportf (dep_sum_set_fam _ _) p xx)
    =
    transportf Y (dep_sum_set_fam_el_transportf_path p xx) (dep_sum_set_fam_el xx).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition dep_sum_set_fam_el_eq
            {X₁ X₂ : hSet}
            {s : X₁ → X₂}
            {Y : X₁ → hSet}
            {y : X₂}
            {xx₁ xx₂ : dep_sum_set_fam s Y y}
            (p : xx₁ = xx₂)
  : dep_sum_set_fam_el xx₁
    =
    transportf Y (!(maponpaths pr1 p)) (dep_sum_set_fam_el xx₂).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Definition dep_sum_set_fam_unit
           {X₁ X₂ : hSet}
           (s : X₁ → X₂)
           (Y : X₁ → hSet)
           {x : X₁}
           (xx : Y x)
  : dep_sum_set_fam s Y (s x)
  := make_dep_sum_set_fam x xx (idpath _).

Definition dep_sum_set_fam_pr
           {X₁ X₂ : hSet}
           {s : X₁ → X₂}
           (Y : X₁ → hSet)
           (Y' : X₂ → hSet)
           (f : ∏ (x : X₁), Y x → Y' (s x))
           {x : X₂}
           (xx : dep_sum_set_fam s Y x)
  : Y' x
  := transportf Y' (dep_sum_set_fam_path xx) (f _ (dep_sum_set_fam_el xx)).

(** * 2. Dependent products of families of sets *)
Definition dep_prod_set_fam
           {X₁ X₂ : hSet}
           (f : X₁ → X₂)
           (Y : X₁ → hSet)
           (y : X₂)
  : hSet
  := (∏ (x : hfiber_hSet f y), Y (pr1 x))%set.

Proposition dep_prod_set_fam_eq
            {X₁ X₂ : hSet}
            {f : X₁ → X₂}
            {Y : X₁ → hSet}
            {y : X₂}
            {ff₁ ff₂ : dep_prod_set_fam f Y y}
            (p : ∏ (x : hfiber_hSet f y), ff₁ x = ff₂ x)
  : ff₁ = ff₂.
Proof.
  use funextsec.
  exact p.
Qed.

Definition dep_prod_set_fam_eval
           {X₁ X₂ : hSet}
           {f : X₁ → X₂}
           {Y : X₁ → hSet}
           (x : X₁)
           (ff : dep_prod_set_fam f Y (f x))
  : Y x
  := ff (x ,, idpath _).

Arguments dep_prod_set_fam_eval /.

Definition dep_prod_set_fam_lam
           {X₁ X₂ : hSet}
           {f : X₁ → X₂}
           {Y : X₁ → hSet}
           (Y' : X₂ → hSet)
           (ff : ∏ (x : X₁), Y' (f x) → Y x)
           {y : X₂}
           (yy : Y' y)
  : dep_prod_set_fam f Y y
  := λ x, ff _ (transportf Y' (!(pr2 x)) yy).

Arguments dep_prod_set_fam_lam /.

(** * 3. Sections of families *)
Definition section_set_fam
           {X : hSet}
           (Y : X → hSet)
  : UU
  := ∏ (x : X), Y x.

Proposition isaset_section_set_fam
            {X : hSet}
            (Y : X → hSet)
  : isaset (section_set_fam Y).
Proof.
  use impred_isaset ; intro.
  apply setproperty.
Qed.
