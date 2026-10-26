/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Norm of a finite-free algebra element from arbitrary scalar-valued coordinates

The signed constant coefficient of the native characteristic-polynomial family of
left multiplication evaluates to the norm of the corresponding element after base change.
-/

set_option warningAsError true

open Module MvPolynomial
open scoped TensorProduct

namespace Algebra

variable {R B A ι : Type*} [CommRing R] [Ring B] [Algebra R B]
  [CommRing A] [Algebra R A] [Fintype ι]

private theorem lmul_family_baseChange :
    (LinearMap.tensorProduct R A B B).comp
      ((Algebra.lmul R B).toLinearMap.baseChange A) =
        (Algebra.lmul A (A ⊗[R] B)).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
    change a • (Algebra.lmul R B z).baseChange A =
      Algebra.lmul A (A ⊗[R] B) (a ⊗ₜ[R] z)
    rw [Algebra.baseChange_lmul]
    have ht : (a ⊗ₜ[R] z : A ⊗[R] B) = a • (1 ⊗ₜ[R] z) :=
      TensorProduct.tmul_eq_smul_one_tmul a z
    rw [ht, map_smul]
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

private theorem basis_coordinates (b : Basis ι R B) (x : ι → A) :
    (TensorProduct.basis A b).repr.symm (Finsupp.equivFunOnFinite.symm x) =
      ∑ i, (x i) ⊗ₜ[R] (b i) := by
  classical
  rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype (Finsupp.equivFunOnFinite.symm x)
    (fun i a ↦ a • (TensorProduct.basis A b) i) (by simp)]
  simp only [Finsupp.coe_equivFunOnFinite_symm, TensorProduct.basis_repr_symm_apply']

public section

/-- Specializing the signed constant characteristic coefficient of left multiplication
at arbitrary coordinates in a commutative base algebra gives the norm after tensor base change. -/
theorem norm_coordinates_baseChange [DecidableEq ι] [Module.Free R B] [Module.Finite R B]
    (b : Basis ι R B) (x : ι → A) :
    MvPolynomial.aeval x
        (MvPolynomial.C ((-1 : R) ^ Module.finrank R B) *
          (LinearMap.polyCharpoly (Algebra.lmul R B).toLinearMap b).coeff 0) =
      Algebra.norm A (∑ i, (x i) ⊗ₜ[R] (b i) : A ⊗[R] B) := by
  classical
  have : Module.Free A (A ⊗[R] B) := Module.Free.of_basis (TensorProduct.basis A b)
  have : Module.Finite A (A ⊗[R] B) := Module.Finite.of_basis (TensorProduct.basis A b)
  nontriviality A
  have : Nontrivial R := (algebraMap R A).domain_nontrivial
  have hrank : Module.finrank R B = Module.finrank A (A ⊗[R] B) := by
    rw [Module.finrank_eq_card_basis b,
      Module.finrank_eq_card_basis (TensorProduct.basis A b)]
  have hpoly := LinearMap.polyCharpolyAux_map_aeval
    (Algebra.lmul R B).toLinearMap b b A x
  have hfamily := lmul_family_baseChange (R := R) (B := B) (A := A)
  rw [← LinearMap.polyCharpolyAux_basisIndep (Algebra.lmul R B).toLinearMap b
    (Module.Free.chooseBasis R B) b] at hpoly
  change (LinearMap.polyCharpoly (Algebra.lmul R B).toLinearMap b).map
    (MvPolynomial.aeval x).toRingHom = _ at hpoly
  rw [hfamily] at hpoly
  rw [← basis_coordinates b x, Algebra.norm_apply,
    LinearMap.det_eq_sign_charpoly_coeff]
  simp only [map_mul, map_pow, map_neg, map_one, ← hrank]
  congr 1
  have hcoeff := congrArg (fun p : Polynomial A ↦ p.coeff 0) hpoly
  convert hcoeff using 1
  · simp only [Polynomial.coeff_map]
    rfl
  · rfl

/-- The native signed characteristic coefficient is itself the norm of the
universal tensor element over the multivariate polynomial ring. -/
theorem norm_universalCoordinates [DecidableEq ι] [Module.Free R B] [Module.Finite R B]
    (b : Basis ι R B) :
    MvPolynomial.C ((-1 : R) ^ Module.finrank R B) *
        (LinearMap.polyCharpoly (Algebra.lmul R B).toLinearMap b).coeff 0 =
      Algebra.norm (MvPolynomial ι R)
        (∑ i, MvPolynomial.X i ⊗ₜ[R] (b i) :
          MvPolynomial ι R ⊗[R] B) := by
  simpa only [MvPolynomial.aeval_X_left, AlgHom.id_apply] using
    norm_coordinates_baseChange (A := MvPolynomial ι R) b MvPolynomial.X

end

end Algebra
