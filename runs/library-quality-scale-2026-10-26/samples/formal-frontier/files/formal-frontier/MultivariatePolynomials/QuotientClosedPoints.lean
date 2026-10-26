/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.EvaluationIdeal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Closed points of polynomial quotients in coordinates

For an arbitrary ideal of a polynomial algebra in finitely many variables over an
algebraically closed field, its zero locus is canonically equivalent to the closed
points of the spectrum of the quotient. A tuple gives the kernel of its descended
evaluation, and the inverse reads the coordinates of a maximal ideal. The
coefficient-field and variable-type universes are independent.

This compares point sets, even when the quotient is nonreduced; it does not
identify topologies, structure sheaves or affine-variety categories.

## References

* R. Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, §3.6.9 and
  the discussion following Exercise 5.1.E (October 21, 2025 draft).
* Mathlib's finite-variable Nullstellensatz, quotient, multivariate-polynomial
  and prime-spectrum formalizations; the earlier Formal Frontier coordinate
  experiment supplies quotient evaluation and its basic laws, but not a proof
  of the closed-point equivalence.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v

variable {K : Type u} {σ : Type v} [Field K]

/-- Evaluation at a tuple annihilating `I` descends to the quotient by `I`. -/
def zeroLocusQuotientEval (I : Ideal (MvPolynomial σ K)) (a : zeroLocus K I) :
    (MvPolynomial σ K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (aeval a.val) (fun p hp => a.property p hp)

/-- Descended evaluation composed with the quotient map is ordinary evaluation. -/
theorem zeroLocusQuotientEval_comp (I : Ideal (MvPolynomial σ K)) (a : zeroLocus K I) :
    (zeroLocusQuotientEval I a).comp (Ideal.Quotient.mkₐ K I) = aeval a.val := by
  exact Ideal.Quotient.liftₐ_comp I (aeval a.val) (fun p hp => a.property p hp)

/-- Descended evaluation sends the class of a polynomial to its value at the tuple. -/
theorem zeroLocusQuotientEval_mk (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) (p : MvPolynomial σ K) :
    zeroLocusQuotientEval I a (Ideal.Quotient.mkₐ K I p) = aeval a.val p := by
  exact AlgHom.congr_fun (zeroLocusQuotientEval_comp I a) p

/-- The quotient class of a variable evaluates to the corresponding coordinate. -/
theorem zeroLocusQuotientEval_X (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) (s : σ) :
    zeroLocusQuotientEval I a (Ideal.Quotient.mkₐ K I (X s)) = a.val s := by
  simpa using zeroLocusQuotientEval_mk I a (X s)

/-- The closed quotient-spectrum point with ideal the kernel of evaluation at a zero. -/
def zeroLocusClosedPoint (I : Ideal (MvPolynomial σ K)) (a : zeroLocus K I) :
    closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I)) := by
  let f := (zeroLocusQuotientEval I a).toRingHom
  have hf : Function.Surjective f := by
    intro c
    refine ⟨Ideal.Quotient.mkₐ K I (C c), ?_⟩
    exact (zeroLocusQuotientEval_mk I a (C c)).trans (by simp)
  have hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  exact ⟨⟨RingHom.ker f, hmax.isPrime⟩,
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax⟩

/-- The ideal of the closed point attached to a zero is the kernel of descended
evaluation, without finiteness or algebraic-closure assumptions. -/
theorem zeroLocusClosedPoint_asIdeal (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    (zeroLocusClosedPoint I a).val.asIdeal =
      RingHom.ker (zeroLocusQuotientEval I a).toRingHom := rfl

/-- A quotient polynomial belongs to the closed point attached to a zero exactly
when the polynomial vanishes at that zero, for any field and variable type. -/
theorem zeroLocusClosedPoint_mem_iff (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) (p : MvPolynomial σ K) :
    (Ideal.Quotient.mkₐ K I p) ∈ (zeroLocusClosedPoint I a).val.asIdeal ↔
      aeval a.val p = 0 := by
  change zeroLocusQuotientEval I a (Ideal.Quotient.mkₐ K I p) = 0 ↔ _
  rw [zeroLocusQuotientEval_mk]

variable [IsAlgClosed K] [Finite σ]

omit [IsAlgClosed K] [Finite σ] in
private theorem closedPoint_comap_isMaximal (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I))) :
    (x.val.asIdeal.comap (Ideal.Quotient.mk I)).IsMaximal := by
  have hmax : x.val.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x.val).1 x.property
  exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (H := hmax)

/-- The zero of an ideal whose coordinates are read from a closed quotient prime. -/
def closedPointZeroLocus (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I))) : zeroLocus K I := by
  let hmax : (x.val.asIdeal.comap (Ideal.Quotient.mk I)).IsMaximal := by
    have h : x.val.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal x.val).1 x.property
    exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (H := h)
  let witness := eq_vanishingIdeal_singleton_of_isMaximal K hmax
  let coordinates := Classical.choose witness
  have hcoordinates : x.val.asIdeal.comap (Ideal.Quotient.mk I) =
      vanishingIdeal K {coordinates} := Classical.choose_spec witness
  exact ⟨coordinates, by
    intro p hp
    apply (mem_vanishingIdeal_singleton_iff coordinates p).mp
    rw [← hcoordinates]
    change (Ideal.Quotient.mkₐ K I p) ∈ x.val.asIdeal
    rw [show Ideal.Quotient.mkₐ K I p = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    exact (x.val.asIdeal).zero_mem⟩

/-- The contraction of a closed quotient prime is the vanishing ideal of the
coordinates read from that prime. -/
theorem closedPointZeroLocus_ideal (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I))) :
    x.val.asIdeal.comap (Ideal.Quotient.mk I) =
      vanishingIdeal K {(closedPointZeroLocus I x).val} := by
  change x.val.asIdeal.comap (Ideal.Quotient.mk I) =
    vanishingIdeal K {Classical.choose (eq_vanishingIdeal_singleton_of_isMaximal K
      (closedPoint_comap_isMaximal I x))}
  exact Classical.choose_spec (eq_vanishingIdeal_singleton_of_isMaximal K
    (closedPoint_comap_isMaximal I x))

/-- Membership in a closed quotient prime is evaluation at its inverse tuple
vanishing on every polynomial. -/
theorem closedPointZeroLocus_mem_iff (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I)))
    (p : MvPolynomial σ K) :
    (Ideal.Quotient.mkₐ K I p) ∈ x.val.asIdeal ↔
      aeval (closedPointZeroLocus I x).val p = 0 := by
  change p ∈ x.val.asIdeal.comap (Ideal.Quotient.mk I) ↔ _
  rw [closedPointZeroLocus_ideal, mem_vanishingIdeal_singleton_iff]

/-- An inverse coordinate equals `c` precisely when the corresponding variable
class minus `c` lies in the closed quotient prime. -/
theorem closedPointZeroLocus_coordinate (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I))) (s : σ) (c : K) :
    (closedPointZeroLocus I x).val s = c ↔
      (Ideal.Quotient.mkₐ K I (X s - C c)) ∈ x.val.asIdeal := by
  rw [closedPointZeroLocus_mem_iff]
  simp only [map_sub, aeval_X, aeval_C, sub_eq_zero,
    Algebra.algebraMap_self_apply]

/-- The canonical correspondence between zeros of an arbitrary polynomial ideal
and closed points of its quotient spectrum. Forward points have as ideal the
kernel of descended evaluation; inverse points read the unique coordinate
values in the base field. Following Vakil, *The Rising Sea*, §3.6.9 and the
discussion after Exercise 5.1.E (October 21, 2025 draft), the point-set
statement also permits nonreduced quotients, unlike the reduced affine-variety
convention. -/
def zeroLocusEquivClosedPoints (I : Ideal (MvPolynomial σ K)) :
    zeroLocus K I ≃ closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I)) where
  toFun := zeroLocusClosedPoint I
  invFun := closedPointZeroLocus I
  left_inv := by
    intro a
    apply Subtype.ext
    funext s
    have hmem : (Ideal.Quotient.mkₐ K I (X s - C (a.val s))) ∈
        (zeroLocusClosedPoint I a).val.asIdeal :=
      (zeroLocusClosedPoint_mem_iff I a _).2 (by simp)
    have h := (closedPointZeroLocus_mem_iff I (zeroLocusClosedPoint I a) _).1 hmem
    exact sub_eq_zero.mp (by simpa using h)
  right_inv := by
    intro x
    apply Subtype.ext
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact (zeroLocusClosedPoint_mem_iff I (closedPointZeroLocus I x) p).trans
      (closedPointZeroLocus_mem_iff I x p).symm

/-- The forward map of the equivalence is the field-only closed-point map. -/
theorem zeroLocusEquivClosedPoints_apply (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    zeroLocusEquivClosedPoints I a = zeroLocusClosedPoint I a := rfl

/-- The inverse map of the equivalence is the closed-prime coordinate map. -/
theorem zeroLocusEquivClosedPoints_symm_apply (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I))) :
    (zeroLocusEquivClosedPoints I).symm x = closedPointZeroLocus I x := rfl

/-- The prime of a zero is the kernel of its descended evaluation. -/
theorem zeroLocusEquivClosedPoints_asIdeal (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    ((zeroLocusEquivClosedPoints I a).val).asIdeal =
      RingHom.ker (zeroLocusQuotientEval I a).toRingHom := by
  rw [zeroLocusEquivClosedPoints_apply]
  exact zeroLocusClosedPoint_asIdeal I a

/-- Membership of a quotient polynomial in the prime of a tuple is vanishing. -/
theorem zeroLocusEquivClosedPoints_mem_iff (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) (p : MvPolynomial σ K) :
    (Ideal.Quotient.mkₐ K I p) ∈ (zeroLocusEquivClosedPoints I a).val.asIdeal ↔
      aeval a.val p = 0 := by
  rw [zeroLocusEquivClosedPoints_apply]
  exact zeroLocusClosedPoint_mem_iff I a p

/-- The inverse tuple detects membership of every quotient polynomial in the
given closed prime by evaluation. -/
theorem zeroLocusEquivClosedPoints_symm_mem_iff (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I)))
    (p : MvPolynomial σ K) :
    (Ideal.Quotient.mkₐ K I p) ∈ x.val.asIdeal ↔
      aeval ((zeroLocusEquivClosedPoints I).symm x).val p = 0 := by
  rw [zeroLocusEquivClosedPoints_symm_apply]
  exact closedPointZeroLocus_mem_iff I x p

/-- An inverse coordinate is the scalar whose difference from the corresponding
variable class belongs to the closed prime. -/
theorem zeroLocusEquivClosedPoints_symm_coordinate (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I))) (s : σ) (c : K) :
    ((zeroLocusEquivClosedPoints I).symm x).val s = c ↔
      (Ideal.Quotient.mkₐ K I (X s - C c)) ∈ x.val.asIdeal := by
  rw [zeroLocusEquivClosedPoints_symm_apply]
  exact closedPointZeroLocus_coordinate I x s c

/-- Taking the closed point of a tuple and reading its coordinates returns the tuple. -/
theorem zeroLocusEquivClosedPoints_symm_apply_apply (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    (zeroLocusEquivClosedPoints I).symm (zeroLocusEquivClosedPoints I a) = a :=
  (zeroLocusEquivClosedPoints I).symm_apply_apply a

/-- Each closed point is recovered from the tuple of its inverse coordinates. -/
theorem zeroLocusEquivClosedPoints_apply_symm_apply (I : Ideal (MvPolynomial σ K))
    (x : closedPoints (PrimeSpectrum (MvPolynomial σ K ⧸ I))) :
    zeroLocusEquivClosedPoints I ((zeroLocusEquivClosedPoints I).symm x) = x :=
  (zeroLocusEquivClosedPoints I).apply_symm_apply x

end MvPolynomial
