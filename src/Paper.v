(**
   This file contains the identifiers in the formalization for the
   paper "Impredicativity in Linear Dependent Type Theory"
   by Sam Speight and Niels van der Weide
 *)
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
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Adjunctions.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.

Require Import PreservesMonoidalClosed.
Require Import FiberwiseMonoidal.
Require Import Basics.BIAlgebra.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Completeness.
Require Import Basics.Combinators.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCompleteness.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Assemblies.LinearAssemblyMonoidal.
Require Import Assemblies.ModestSet.
Require Import Assemblies.PartialEqRel.
Require Import Assemblies.ModestSetEquiv.
Require Import Types.LinearCompCat.
Require Import Types.DependentSums.
Require Import Types.DependentProducts.
Require Import Types.FiberAssembly.
Require Import Types.LinearFiber.
Require Import Types.LinearNonLinear.
Require Import Types.LinearSigma.
Require Import Types.LinearPi.
Require Import Types.Terms.
Require Import Types.LinearRealizabilityModel.
Require Import Types.ImpredicativeUniverse.

Local Open Scope cat.

(** Section 3 *)

(** Definition 3.1: applicative structure*)
Definition def_3_1_pas := @applicative_structure.

(** Definition 3.2: combinatory algebras *)
Definition def_3_2_ca := @combinatory_algebra.

(** Definition 3.3: linear combinatory algebra *)
Definition def_3_3_lca := @linear_combinatory_algebra.

(** Proposition 3.4: combinatory completeness *)
Definition prop_3_4_term := @lam_term.
Definition prop_3_4_beta_m := @lam_term_multiple.
Definition prop_3_4_beta_s := @lam_term_single.

(** Proposition 3.5: linear combinatory completeness *)
Definition prop_3_5_term_lin := @lam_lin_term_linear.
Definition prop_3_5_term_nonlin := @lam_lin_term_nonlinear.
Definition prop_3_5_beta_lin := @lam_lin_term_beta.
Definition prop_3_5_beta_nonlin := @lam_lin_term_nonlinear_beta.

(** Section 4 *)
(**
   There are various examples in this section, which show how the linear realizability
   model is defined. Example 4.14 builds forth upon Examples 4.5, 4.7, 4.10, and 4.12.
   For this reason, we only mention Examples 4.14 and 4.17 below.
 *)

(** Definition 4.1: Cartesian morphisms and Grothendieck fibrations *)

(**
   Whereas in the paper we use a set-theoretic notation, we use displayed categories
   in the formalization
 *)
Definition def_4_1_cartesian := @Fibrations.is_cartesian.
Definition def_4_1_fibration := @cleaving.

(** Definition 4.2: Comprehension categories *)
(**
   Note that we do not reuse this notion to define linear comprehension categories.
 *)
Definition def_4_2_comp_cat := @comprehension_cat_structure.

(** Definition 4.4: ∏-types and ∑-types *)
(**
   Note that we formulate strong ∑-types for linear comprehension categories
 *)
Definition def_4_4_prod := @has_dependent_products.
Definition def_4_4_sigma := @has_dependent_sums.
Definition def_4_4_strong_sigma := @strong_cartesian_dep_sums.

(** Definition 4.7: symmetric monoidal closed fibrations *)
(**
   In the formalization, we define fiberwise symmetric monoidal fibrations,
   and linear function types are seen as structure on a comprehension categories.
   In the paper, we combine these notions, and in the formalization, that would
   be represented by the conjunction of the following two definitions.
 *)
Definition def_4_7_fibration := @fiberwise_symmetric_monoidal_structure.
Definition def_4_7_functions := @linear_function_types.

(** Definition 4.9: linear comprehension categories *)
Definition def_4_9_linear_comp_cat := @linear_comp_cat_structure.

(** Proposition 4.10: monoidal adjunctions *)
Definition prop_4_10_adjunction := @sym_monoidal_adjunction_from_strong.

(** Definition 4.12: linear ∏ and ∑-types *)
Definition def_4_12_prod := @linear_dep_products.
Definition def_4_12_sig := @linear_dep_sums_frobenius.

(** Definition 4.14: fiberwise equalizer *)
Definition def_4_14_fiberwise_equalizer := @fiberwise_equalizers.

(** Example 4.15: linear realizability model *)
Definition exa_4_15_model := @realizability_linear_comp_cat_structure_types.
Definition exa_4_15_M_ff := @lin_dep_to_dep_assembly_morphism_faithful.
Definition exa_4_15_L_ff := @dep_to_lin_dep_assembly_morphism_faithful.
Definition exa_4_15_equalizers := @fiberwise_equalizers_lin_dep_assembly.

(** Definition 4.16: modest sets and partial equivalence relations *)
Definition def_4_16_modest := @is_modest.
Definition def_4_16_per := @ca_per.

(** Theorem 4.17: modest sets and PERs are equivalent *)
Definition thm_4_17_equiv := @ca_per_modeset_set_equivalence.

(** Example 4.18: impredicative universe *)
Definition exa_4_18_univ := @assembly_universe_type.
Definition exa_4_18_cartesian_iso := @is_modest_dep_assembly_ca_per_z_iso.
Definition exa_4_18_linear_iso := @is_modest_lin_dep_assembly_ca_per_z_iso.
Definition exa_4_18_cartesian_prod_modest := @is_modest_lin_dep_assembly_ca_per_z_iso.
Definition exa_4_18_linear_prod_modest := @is_modest_family_linear_dep_prod.
