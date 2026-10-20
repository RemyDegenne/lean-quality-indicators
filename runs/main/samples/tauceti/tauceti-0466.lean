public section

namespace OrthogonalIdempotents

open TauCeti

variable {R ι : Type*} [Semiring R] [Fintype ι] {P Q : ι → R}

@[simp]
theorem projectionFamilyOverlap_mul (hP : OrthogonalIdempotents P) (Q : ι → R) (i : ι) :
    projectionFamilyOverlap P Q * P i = Q i * P i := by
  classical
  simp [projectionFamilyOverlap_def, Finset.sum_mul, mul_assoc, hP.mul_eq, mul_ite]

end OrthogonalIdempotents
end
