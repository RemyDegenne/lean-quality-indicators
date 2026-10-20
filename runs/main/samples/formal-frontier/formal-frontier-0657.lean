public section

open Function Set

open CategoryTheory

universe u v w

namespace CompleteOrthogonalIdempotents

theorem prod_mul {S : Type u} {I : Type v} {J : Type w}
    [Semiring S] [Fintype I] [Fintype J] {e : I → S} {f : J → S}
    (he : CompleteOrthogonalIdempotents e) (hf : CompleteOrthogonalIdempotents f)
    (hcomm : ∀ i j, Commute (e i) (f j)) :
    CompleteOrthogonalIdempotents (fun ij : I × J ↦ e ij.1 * f ij.2) := by
  classical
  apply CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
  constructor
  · intro ij kl hij
    calc
      (e ij.1 * f ij.2) * (e kl.1 * f kl.2) =
          e ij.1 * (f ij.2 * e kl.1) * f kl.2 := by simp only [mul_assoc]
      _ = e ij.1 * (e kl.1 * f ij.2) * f kl.2 := by
        rw [← (hcomm kl.1 ij.2).eq]
      _ = (e ij.1 * e kl.1) * (f ij.2 * f kl.2) := by simp only [mul_assoc]
      _ = 0 := by
        by_cases hi : ij.1 = kl.1
        · have hj : ij.2 ≠ kl.2 := fun hj ↦ hij (Prod.ext hi hj)
          rw [hf.ortho hj, mul_zero]
        · rw [he.ortho hi, zero_mul]
  · calc
      ∑ ij : I × J, e ij.1 * f ij.2 = ∑ i : I, ∑ j : J, e i * f j :=
        Fintype.sum_prod_type _
      _ = (∑ i : I, e i) * ∑ j : J, f j := (Fintype.sum_mul_sum e f).symm
      _ = 1 := by rw [he.complete, hf.complete, one_mul]

end CompleteOrthogonalIdempotents
end
