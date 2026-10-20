public section

namespace CliffordAlgebra

open TauCeti

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

section Scalar

variable {K : Type u} [Field K] [Module K M]

theorem neg_one_mem_spinGroup (Q : QuadraticForm K M) (hQ : Q ≠ 0) :
    (-1 : CliffordAlgebra Q) ∈ spinGroup Q := by
  obtain ⟨v, hv⟩ := QuadraticMap.exists_isUnit_of_ne_zero hQ
  exact neg_one_mem_spinGroup_of_isUnit Q v hv

end Scalar
end CliffordAlgebra
end
