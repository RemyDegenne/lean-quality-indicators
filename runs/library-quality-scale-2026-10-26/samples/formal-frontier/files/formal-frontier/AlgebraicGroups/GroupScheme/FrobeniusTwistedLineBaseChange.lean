/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.FrobeniusTwistedLine

/-!
# Base change of a Frobenius-twisted additive line

This file gives an explicit normal form for `FrobeniusTwistedLine.CoordinateRing` after a
scalar extension that contains a chosen `p`-th root of the twisting parameter.

The normal-form ring is the literal two-variable quotient

`L[W, X] / (W ^ p)`.

Thus `X` is a free line coordinate, while `W` is the transverse infinitesimal coordinate with
the sole relation `W ^ p = 0`.  The equivalence sends the original coordinates to

`X ↦ X`,  `Y ↦ W + α X`,

and hence sends the translated coordinate `Y - α X` to `W`.  Both directions of these
coordinate formulas are exposed as simp lemmas.

Milne's *Algebraic Groups*, Example 1.27, describes the resulting line
as having multiplicity `p`. This file establishes the explicit quotient
presentation and translated-coordinate equations, not a separate geometric
or cycle-theoretic multiplicity predicate. The equivalence is an algebra
equivalence after extension to a field `L` with a chosen `α : L` satisfying
`α ^ p = t`; `L` may have a different universe size from the base field.

## Main definitions

- `FrobeniusTwistedLine.ThickenedLineCoordinateRing`
- `FrobeniusTwistedLine.baseChangeNormalForm`

## Main results

- `FrobeniusTwistedLine.thickenedLineW_pow`
- `FrobeniusTwistedLine.baseChangeNormalForm_tmul_x`
- `FrobeniusTwistedLine.baseChangeNormalForm_tmul_y`
- `FrobeniusTwistedLine.baseChangeNormalForm_witness`
- `FrobeniusTwistedLine.baseChangeNormalForm_symm_x`
- `FrobeniusTwistedLine.baseChangeNormalForm_symm_w`

## References

- James S. Milne, *Algebraic Groups* (2017), Example 1.27, p. 14 (the
  `p`-th-root base change and multiplicity-`p` line description).
- `AlgebraicGroups.GroupScheme.FrobeniusTwistedLine` (the quotient relation,
  scalar-extended coordinate and nilpotent witness used in the normal form).
- Mathlib, `Mathlib.Algebra.CharP.Lemmas` and the `MvPolynomial` and
  `Ideal.Quotient` algebra-map APIs (characteristic-power identities and
  evaluation/lifting from the two polynomial quotients).
-/

@[expose] public section

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

universe u v

/-- The equation `W ^ p` defining the transverse infinitesimal coordinate of an order-`p`
thickening. -/
def thickenedLineEquation (L : Type v) [CommRing L] (p : ℕ) : MvPolynomial (Fin 2) L :=
  MvPolynomial.X 0 ^ p

/-- The coordinate ring `L[W, X] / (W ^ p)` of a line with its order-`p` infinitesimal
thickening. Coordinate `0` is `W` and coordinate `1` is `X`. -/
abbrev ThickenedLineCoordinateRing (L : Type v) [CommRing L] (p : ℕ) :=
  MvPolynomial (Fin 2) L ⧸ Ideal.span {thickenedLineEquation L p}

/-- The free line coordinate in `ThickenedLineCoordinateRing`. -/
def thickenedLineX (L : Type v) [CommRing L] (p : ℕ) : ThickenedLineCoordinateRing L p :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The transverse infinitesimal coordinate in `ThickenedLineCoordinateRing`. -/
def thickenedLineW (L : Type v) [CommRing L] (p : ℕ) : ThickenedLineCoordinateRing L p :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The sole relation in the transverse coordinate is `W ^ p = 0`. -/
@[simp]
theorem thickenedLineW_pow (L : Type v) [CommRing L] (p : ℕ) :
    thickenedLineW L p ^ p = 0 := by
  change Ideal.Quotient.mk _ (thickenedLineEquation L p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

section ThickenedLine

variable (L : Type v) [CommRing L]

/-- Evaluation of `W` and `X` at a pair of elements. -/
def thickenedLineEval {A : Type*} [CommRing A] [Algebra L A] (_p : ℕ) (x' w' : A) :
    MvPolynomial (Fin 2) L →ₐ[L] A :=
  MvPolynomial.aeval fun i ↦ Fin.cases w' (fun _ ↦ x') i

theorem thickenedLineSpan_le_ker_eval {A : Type*} [CommRing A] [Algebra L A]
    (p : ℕ) (x' w' : A) (hw : w' ^ p = 0) :
    Ideal.span {thickenedLineEquation L p} ≤
      RingHom.ker (thickenedLineEval L p x' w').toRingHom := by
  apply Ideal.span_le.mpr
  rw [Set.singleton_subset_iff]
  apply RingHom.mem_ker.mpr
  change thickenedLineEval L p x' w' (thickenedLineEquation L p) = 0
  simpa [thickenedLineEval, thickenedLineEquation] using hw

/-- The universal map from `L[W, X] / (W ^ p)` to a ring containing an element `w'` with
`w' ^ p = 0` and an arbitrary element `x'`. -/
def thickenedLineLift {A : Type*} [CommRing A] [Algebra L A]
    (p : ℕ) (x' w' : A) (hw : w' ^ p = 0) :
    ThickenedLineCoordinateRing L p →ₐ[L] A :=
  Ideal.Quotient.liftₐ _ (thickenedLineEval L p x' w') fun _f hf ↦
    RingHom.mem_ker.mp (thickenedLineSpan_le_ker_eval L p x' w' hw hf)

theorem thickenedLineLift_comp_mk {A : Type*} [CommRing A] [Algebra L A]
    (p : ℕ) (x' w' : A) (hw : w' ^ p = 0) :
    (thickenedLineLift L p x' w' hw).comp
      (Ideal.Quotient.mkₐ L (Ideal.span {thickenedLineEquation L p})) =
        thickenedLineEval L p x' w' := by
  apply Ideal.Quotient.liftₐ_comp

@[simp]
theorem thickenedLineLift_x {A : Type*} [CommRing A] [Algebra L A]
    (p : ℕ) (x' w' : A) (hw : w' ^ p = 0) :
    thickenedLineLift L p x' w' hw (thickenedLineX L p) = x' := by
  change ((thickenedLineLift L p x' w' hw).comp
    (Ideal.Quotient.mkₐ L (Ideal.span {thickenedLineEquation L p})))
      (MvPolynomial.X 1) = x'
  rw [thickenedLineLift_comp_mk]
  simp only [thickenedLineEval, MvPolynomial.aeval_X]
  rfl

@[simp]
theorem thickenedLineLift_w {A : Type*} [CommRing A] [Algebra L A]
    (p : ℕ) (x' w' : A) (hw : w' ^ p = 0) :
    thickenedLineLift L p x' w' hw (thickenedLineW L p) = w' := by
  change ((thickenedLineLift L p x' w' hw).comp
    (Ideal.Quotient.mkₐ L (Ideal.span {thickenedLineEquation L p})))
      (MvPolynomial.X 0) = w'
  rw [thickenedLineLift_comp_mk]
  simp only [thickenedLineEval, MvPolynomial.aeval_X, Fin.cases_zero]

@[ext]
theorem thickenedLineHom_ext {A : Type*} [Semiring A] [Algebra L A]
    {p : ℕ} {f g : ThickenedLineCoordinateRing L p →ₐ[L] A}
    (hx : f (thickenedLineX L p) = g (thickenedLineX L p))
    (hw : f (thickenedLineW L p) = g (thickenedLineW L p)) : f = g := by
  rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective L _)]
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa [thickenedLineW] using hw
  · have : j = 0 := Subsingleton.elim _ _
    subst j
    simpa [thickenedLineX] using hx

/-- Evaluation of the thickened line at its origin. -/
def thickenedLineOrigin {p : ℕ} [Fact p.Prime] :
    ThickenedLineCoordinateRing L p →ₐ[L] L :=
  thickenedLineLift L p 0 0 (by simp [(Fact.out : p.Prime).ne_zero])

instance thickenedLineCoordinateRing_nontrivial {p : ℕ} [Fact p.Prime] [Nontrivial L] :
    Nontrivial (ThickenedLineCoordinateRing L p) :=
  (thickenedLineOrigin L).domain_nontrivial

instance thickenedLineCoordinateRing_charP {p : ℕ} [Fact p.Prime]
    [CharP L p] :
    CharP (ThickenedLineCoordinateRing L p) p := by
  have hinj : Function.Injective
      (algebraMap L (ThickenedLineCoordinateRing L p)) := by
    intro a b hab
    have h := congrArg (thickenedLineOrigin L) hab
    simpa using h
  exact charP_of_injective_algebraMap hinj p

end ThickenedLine

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

theorem translatedCoordinates_satisfyEquation {p : ℕ} (hp : p.Prime)
    [CharP K p] (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    SatisfiesEquation (R := K) (A := ThickenedLineCoordinateRing L p) p t
      (thickenedLineX L p)
      (thickenedLineW L p +
        algebraMap L (ThickenedLineCoordinateRing L p) α * thickenedLineX L p) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP L p := CharP.of_ringHom_of_ne_zero (algebraMap K L) p hp.ne_zero
  rw [SatisfiesEquation, add_pow_char, mul_pow, thickenedLineW_pow, zero_add,
    ← map_pow, hα, IsScalarTower.algebraMap_apply K L]
  exact sub_self _

/-- The forward algebra map underlying the base-change normal form. It sends `X` to the free
line coordinate and `Y` to `W + α X`. -/
def baseChangeNormalFormHom {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    L ⊗[K] CoordinateRing K p t →ₐ[L] ThickenedLineCoordinateRing L p := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP L p := CharP.of_ringHom_of_ne_zero (algebraMap K L) p hp.ne_zero
  exact (lift K p t (thickenedLineX L p)
    (thickenedLineW L p +
      algebraMap L (ThickenedLineCoordinateRing L p) α * thickenedLineX L p)
    (translatedCoordinates_satisfyEquation K L hp t α hα)).liftEquiv
      K L (CoordinateRing K p t) (ThickenedLineCoordinateRing L p)

@[simp]
theorem baseChangeNormalFormHom_tmul_x {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalFormHom K L hp t α hα
        ((1 : L) ⊗ₜ[K] x K p t) = thickenedLineX L p := by
  simp [baseChangeNormalFormHom]

@[simp]
theorem baseChangeNormalFormHom_tmul_y {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalFormHom K L hp t α hα
        ((1 : L) ⊗ₜ[K] y K p t) =
      thickenedLineW L p +
        algebraMap L (ThickenedLineCoordinateRing L p) α * thickenedLineX L p := by
  simp [baseChangeNormalFormHom]

@[simp]
theorem baseChangeNormalFormHom_witness {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalFormHom K L hp t α hα (nilpotentWitness K L p t α) =
      thickenedLineW L p := by
  simp [nilpotentWitness, baseChangeNormalFormHom, Algebra.smul_def]

/-- The inverse algebra map underlying the base-change normal form. It sends the free line
coordinate to `1 ⊗ X` and the transverse coordinate `W` to `1 ⊗ Y - α ⊗ X`. -/
def baseChangeNormalFormInv {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    ThickenedLineCoordinateRing L p →ₐ[L] L ⊗[K] CoordinateRing K p t :=
  thickenedLineLift L p ((1 : L) ⊗ₜ[K] x K p t) (nilpotentWitness K L p t α)
    (nilpotentWitness_pow K L hp t α hα)

@[simp]
theorem baseChangeNormalFormInv_x {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalFormInv K L hp t α hα (thickenedLineX L p) =
      (1 : L) ⊗ₜ[K] x K p t := by
  simp [baseChangeNormalFormInv]

@[simp]
theorem baseChangeNormalFormInv_w {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalFormInv K L hp t α hα (thickenedLineW L p) =
      nilpotentWitness K L p t α := by
  simp [baseChangeNormalFormInv]

theorem baseChangeNormalFormHom_comp_inv {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    (baseChangeNormalFormHom K L hp t α hα).comp
        (baseChangeNormalFormInv K L hp t α hα) =
      AlgHom.id L (ThickenedLineCoordinateRing L p) := by
  apply thickenedLineHom_ext <;> simp

theorem baseChangeNormalFormInv_comp_hom {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    (baseChangeNormalFormInv K L hp t α hα).comp
        (baseChangeNormalFormHom K L hp t α hα) =
      AlgHom.id L (L ⊗[K] CoordinateRing K p t) := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  · simp
  · change baseChangeNormalFormInv K L hp t α hα
        (baseChangeNormalFormHom K L hp t α hα ((1 : L) ⊗ₜ[K] y K p t)) =
      (1 : L) ⊗ₜ[K] y K p t
    rw [baseChangeNormalFormHom_tmul_y]
    rw [map_add, baseChangeNormalFormInv_w, map_mul, baseChangeNormalFormInv_x]
    change nilpotentWitness K L p t α +
        (baseChangeNormalFormInv K L hp t α hα)
          (algebraMap L (ThickenedLineCoordinateRing L p) α) *
            ((1 : L) ⊗ₜ[K] x K p t) = (1 : L) ⊗ₜ[K] y K p t
    rw [(baseChangeNormalFormInv K L hp t α hα).commutes α]
    simp [nilpotentWitness, Algebra.TensorProduct.tmul_mul_tmul]

/-- After choosing `α` with `α ^ p = t`, the Frobenius-twisted line of Milne's
*Algebraic Groups*, Example 1.27, has scalar-extended coordinate ring
`L[W, X] / (W ^ p)`. The equivalence identifies `W` with
`1 ⊗ Y - α ⊗ X`; it gives the explicit thickened-line quotient, rather than
a geometric multiplicity predicate. -/
def baseChangeNormalForm {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    L ⊗[K] CoordinateRing K p t ≃ₐ[L] ThickenedLineCoordinateRing L p :=
  AlgEquiv.ofAlgHom
    (baseChangeNormalFormHom K L hp t α hα)
    (baseChangeNormalFormInv K L hp t α hα)
    (baseChangeNormalFormHom_comp_inv K L hp t α hα)
    (baseChangeNormalFormInv_comp_hom K L hp t α hα)

@[simp]
theorem baseChangeNormalForm_tmul_x {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalForm K L hp t α hα ((1 : L) ⊗ₜ[K] x K p t) =
      thickenedLineX L p := by
  simp [baseChangeNormalForm]

@[simp]
theorem baseChangeNormalForm_tmul_y {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalForm K L hp t α hα ((1 : L) ⊗ₜ[K] y K p t) =
      thickenedLineW L p +
        algebraMap L (ThickenedLineCoordinateRing L p) α * thickenedLineX L p := by
  simp [baseChangeNormalForm]

@[simp]
theorem baseChangeNormalForm_witness {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalForm K L hp t α hα (nilpotentWitness K L p t α) =
      thickenedLineW L p := by
  simp [baseChangeNormalForm]

@[simp]
theorem baseChangeNormalForm_symm_x {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    (baseChangeNormalForm K L hp t α hα).symm (thickenedLineX L p) =
      (1 : L) ⊗ₜ[K] x K p t := by
  simp [baseChangeNormalForm]

@[simp]
theorem baseChangeNormalForm_symm_w {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    (baseChangeNormalForm K L hp t α hα).symm (thickenedLineW L p) =
      nilpotentWitness K L p t α := by
  simp [baseChangeNormalForm]

end

end FrobeniusTwistedLine
