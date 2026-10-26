/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.RealClosedAdjoinRoot
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Real quadratic coordinates and complex polynomial quotients

The quadratic algebra with a generator whose square is `-1` has complex
coordinates, with the generator sent to `Complex.I`. An irreducible quadratic
quotient maps to `ℂ` after choosing which complex root is the image of `X`.
For an irreducible nonlinear real polynomial, a root may instead be chosen
noncomputably, without requiring a root or normalization from the caller.

## References

* Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, §3.2,
  Exercise 3.2.B, asks for the real quadratic quotient as complex numbers.
* Mathlib's `Algebra.QuadraticAlgebra.Basic` supplies the generator, its
  universal property and its coordinate decomposition; `Basic.Complex.Basic`
  supplies complex coordinates.
* Mathlib's `Analysis.Complex.Polynomial.Basic` supplies algebraic closure of
  `ℂ` and the degree bound for irreducible real polynomials.
* `QuadraticAlgebras.RealClosedAdjoinRoot` supplies the arbitrary-field
  equivalence for a supplied quadratic root and its evaluation laws.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false

noncomputable section

open Polynomial

namespace QuadraticAlgebra

/-- The real quadratic algebra with `ω² = -1`, identified with `ℂ` so that
`ω` corresponds to `Complex.I`. -/
noncomputable def realComplexEquiv : QuadraticAlgebra ℝ (-1) 0 ≃ₐ[ℝ] ℂ := by
  let f : QuadraticAlgebra ℝ (-1) 0 →ₐ[ℝ] ℂ :=
    lift ⟨Complex.I, by simp [Complex.I_mul_I]⟩
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y hxy
    have hcoord : (x.re : ℂ) + x.im * Complex.I =
        (y.re : ℂ) + y.im * Complex.I := by
      simpa [f, lift_apply_apply, ← Algebra.algebraMap_eq_smul_one] using hxy
    apply QuadraticAlgebra.ext
    · have hre := congrArg Complex.re hcoord
      simpa using hre
    · have him := congrArg Complex.im hcoord
      simpa using him
  · intro z
    refine ⟨⟨z.re, z.im⟩, ?_⟩
    simp [f, lift_apply_apply, ← Algebra.algebraMap_eq_smul_one]

/-- Complex coordinates of an arbitrary element of the quadratic algebra. -/
@[simp] theorem realComplexEquiv_apply (z : QuadraticAlgebra ℝ (-1) 0) :
    realComplexEquiv z = (z.re : ℂ) + z.im * Complex.I := by
  change z.re • (1 : ℂ) + z.im • Complex.I = _
  simp [← Algebra.algebraMap_eq_smul_one]

/-- The distinguished quadratic generator corresponds to the positive
imaginary unit. -/
@[simp] theorem realComplexEquiv_omega :
    realComplexEquiv (omega : QuadraticAlgebra ℝ (-1) 0) = Complex.I := by
  rw [realComplexEquiv_apply]
  simp

/-- The inverse equivalence extracts the real and imaginary coordinates. -/
@[simp] theorem realComplexEquiv_symm_apply (z : ℂ) :
    realComplexEquiv.symm z = ⟨z.re, z.im⟩ := by
  apply realComplexEquiv.injective
  rw [realComplexEquiv.apply_symm_apply, realComplexEquiv_apply]
  exact (Complex.re_add_im z).symm

/-- For an irreducible real quadratic, a specified complex root determines
the equivalence that evaluates polynomial classes at that root. No choice of
square-root sign or monic normalization is imposed. -/
noncomputable def adjoinRootComplexEquivOfRoot (p : ℝ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : ℂ) (hz : p.aeval z = 0) :
    AdjoinRoot p ≃ₐ[ℝ] ℂ := by
  have hz' : p.aeval (realComplexEquiv.symm z) = 0 := by
    apply realComplexEquiv.injective
    rw [map_zero, ← Polynomial.aeval_algHom_apply, realComplexEquiv.apply_symm_apply]
    exact hz
  exact (adjoinRootEquivOfRoot p hp hdeg (realComplexEquiv.symm z) hz').trans
    realComplexEquiv

/-- The supplied-root equivalence sends the polynomial variable to the
supplied complex root. -/
@[simp] theorem adjoinRootComplexEquivOfRoot_root (p : ℝ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : ℂ) (hz : p.aeval z = 0) :
    adjoinRootComplexEquivOfRoot p hp hdeg z hz (AdjoinRoot.root p) = z := by
  simp [adjoinRootComplexEquivOfRoot]

/-- Every polynomial class evaluates at the supplied complex root. -/
theorem adjoinRootComplexEquivOfRoot_mk (p : ℝ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : ℂ) (hz : p.aeval z = 0) (g : ℝ[X]) :
    adjoinRootComplexEquivOfRoot p hp hdeg z hz (AdjoinRoot.mk p g) =
      g.eval₂ (algebraMap ℝ ℂ) z := by
  calc
    _ = realComplexEquiv (g.aeval (realComplexEquiv.symm z)) := by
      rw [adjoinRootComplexEquivOfRoot, AlgEquiv.trans_apply,
        adjoinRootEquivOfRoot_mk, Polynomial.aeval_def]
    _ = g.aeval z := by
      rw [← Polynomial.aeval_algHom_apply, realComplexEquiv.apply_symm_apply]
    _ = _ := by rw [Polynomial.aeval_def]

/-- Real constant classes are preserved under the supplied-root map. -/
@[simp] theorem adjoinRootComplexEquivOfRoot_C (p : ℝ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : ℂ) (hz : p.aeval z = 0) (r : ℝ) :
    adjoinRootComplexEquivOfRoot p hp hdeg z hz (AdjoinRoot.mk p (C r)) = (r : ℂ) := by
  rw [adjoinRootComplexEquivOfRoot_mk]
  simp

/-- A selected complex root of an irreducible real polynomial. This choice
does not impose a sign convention. -/
noncomputable def complexRootOfIrreducible (p : ℝ[X]) (hp : Irreducible p) : ℂ :=
  Classical.choose
    (IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne')

/-- The selected complex number satisfies the polynomial. -/
theorem complexRootOfIrreducible_aeval (p : ℝ[X]) (hp : Irreducible p) :
    p.aeval (complexRootOfIrreducible p hp) = 0 :=
  Classical.choose_spec
    (IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne')

/-- A quotient by an irreducible nonlinear real polynomial is equivalent to
`ℂ`, without a caller-supplied complex root, monicity or discriminant witness.
This gives an `ℝ`-algebra equivalence with chosen polynomial evaluation,
whereas the source asks for an isomorphism of quotient rings. The selected
equivalence need not agree with the opposite-root choice. -/
noncomputable def adjoinRootComplexEquivOfIrreducible (p : ℝ[X])
    (hp : Irreducible p) (hdeg : 1 < p.natDegree) : AdjoinRoot p ≃ₐ[ℝ] ℂ := by
  exact adjoinRootComplexEquivOfRoot p hp
    (Nat.le_antisymm hp.natDegree_le_two (Nat.succ_le_of_lt hdeg))
    (complexRootOfIrreducible p hp) (complexRootOfIrreducible_aeval p hp)

/-- The variable maps to the selected complex root. -/
@[simp] theorem adjoinRootComplexEquivOfIrreducible_root (p : ℝ[X])
    (hp : Irreducible p) (hdeg : 1 < p.natDegree) :
    adjoinRootComplexEquivOfIrreducible p hp hdeg (AdjoinRoot.root p) =
      complexRootOfIrreducible p hp := by
  exact adjoinRootComplexEquivOfRoot_root p hp _ _ _

/-- Every polynomial class evaluates at the selected complex root. -/
theorem adjoinRootComplexEquivOfIrreducible_mk (p : ℝ[X])
    (hp : Irreducible p) (hdeg : 1 < p.natDegree) (g : ℝ[X]) :
    adjoinRootComplexEquivOfIrreducible p hp hdeg (AdjoinRoot.mk p g) =
      g.eval₂ (algebraMap ℝ ℂ) (complexRootOfIrreducible p hp) := by
  exact adjoinRootComplexEquivOfRoot_mk p hp _ _ _ g

/-- Real constant classes are preserved under the witness-free map. -/
@[simp] theorem adjoinRootComplexEquivOfIrreducible_C (p : ℝ[X])
    (hp : Irreducible p) (hdeg : 1 < p.natDegree) (r : ℝ) :
    adjoinRootComplexEquivOfIrreducible p hp hdeg (AdjoinRoot.mk p (C r)) = (r : ℂ) := by
  rw [adjoinRootComplexEquivOfIrreducible_mk]
  simp

end QuadraticAlgebra
