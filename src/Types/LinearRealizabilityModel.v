(**

 The linear realizability model

 In this file, we construct the linear realizability model. The relevant statements
 are proved in other files, so here we only collect them and put them together.
 
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

Require Import PreservesMonoidalClosed.
Require Import FiberwiseMonoidal.
Require Import Basics.BIAlgebra.
Require Import Basics.CombinatoryAlgebra.
Require Import Basics.Combinators.
Require Import Basics.LinearCombinatoryAlgebra.
Require Import Basics.LinearCombinators.
Require Import Assemblies.CatOfAssemblies.
Require Import Assemblies.AssembliesStructure.
Require Import Assemblies.DependentAssembly.
Require Import Assemblies.LinearAssembly.
Require Import Assemblies.LinearAssemblyMonoidal.
Require Import Types.LinearCompCat.
Require Import Types.DependentSums.
Require Import Types.DependentProducts.
Require Import Types.FiberAssembly.
Require Import Types.LinearFiber.
Require Import Types.LinearNonLinear.
Require Import Types.LinearSigma.
Require Import Types.LinearPi.
Require Import Types.Terms.

Local Open Scope cat.

Section RealizabilityModel.
  Context (A : linear_combinatory_algebra).

  Let AC : combinatory_algebra := lca_to_ca A.
  
  Definition realizability_linear_comp_cat_structure
    : linear_comp_cat_structure.
  Proof.
    use make_linear_comp_cat_structure.
    - exact (cat_of_assembly AC).
    - exact (disp_cat_of_dep_assembly AC).
    - exact (disp_cat_of_lin_dep_assembly A).
    - exact (dep_assembly_cleaving AC).
    - exact (lin_dep_assembly_cleaving A).
    - exact (dep_assembly_comprehension AC).
    - exact is_cartesian_dep_assembly_comprehension.
    - exact (disp_functor_ff_dep_assembly_comprehension AC).
    - exact fiberwise_symmetric_monoidal_lin_dep_assembly.
  Defined.

  Definition realizability_linear_comp_cat_structure_types
    : linear_comp_cat_types realizability_linear_comp_cat_structure.
  Proof.
    refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact fiberwise_initial_dep_assembly.
    - exact fiberwise_bincoproducts_dep_assembly.
    - use make_strong_cartesian_dep_sums.
      + exact dep_assembly_dependent_sums.
      + intros.
        apply dep_assembly_dependent_sums_strong.
    - exact dep_assembly_dependent_products.
    - exact (fiberwise_terminal_lin_dep_assembly A).
    - exact fiberwise_initial_lin_dep_assembly.
    - exact fiberwise_binproducts_lin_dep_assembly.
    - exact fiberwise_bincoproducts_lin_dep_assembly.
    - use make_linear_dep_sums_frobenius.
      + exact lin_dep_assembly_dependent_sums.
      + intros Γ Δ X₁ X₂ s.
        exact (is_z_isomorphism_lin_assembly_frobenius_morphism s X₁ X₂).
    - simple refine (_ ,, _).
      + intro Γ.
        exact (pr2 (linear_assembly_sym_mon_closed_cat Γ)).
      + intros Γ Δ s.
        apply preserves_sym_mon_closed_lin_assembly_fiber_functor.
    - exact lin_dep_assembly_dependent_products.
  Defined.
      
  Definition realizability_linear_comp_cat
    : linear_comp_cat.
  Proof.
    use make_linear_comp_cat.
    - exact realizability_linear_comp_cat_structure.
    - exact realizability_linear_comp_cat_structure_types.
    - simple refine (_ ,, _).
      + exact (fiberwise_terminal_dep_assembly AC).
      + exact fiberwise_terminal_z_iso.
    - exact fiberwise_binproducts_dep_assembly.
    - simple refine (_ ,, _ ,, _ ,, _).
      + exact dep_lin_assembly_adjunction.
      + exact is_cartesian_dep_to_lin_assembly.
      + exact is_cartesian_lin_to_dep_assembly.
      + intros Γ.
        simple refine (_ ,, _).
        * exact (fiber_functor_dep_to_lin_monoidal Γ).
        * exact (fiber_functor_dep_to_lin_symmetric_monoidal Γ).
  Defined.
End RealizabilityModel.
