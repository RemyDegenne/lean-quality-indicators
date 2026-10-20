@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v

variable {K : Type u} {σ : Type v} [Field K]

variable [IsAlgClosed K] [Finite σ]

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

end MvPolynomial
end
end
