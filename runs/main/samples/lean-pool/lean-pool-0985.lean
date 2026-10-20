universe u v

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

omit [IsOrderedCancelAddMonoid M] in
theorem componentMk_heq_of_grade_eq_of_sub_lt (ν : MaxAddDegree R M) {m n : M}
    (hmn : m = n) (x : ν.filtrationLE m) (y : ν.filtrationLE n)
    (hxy : ν ((x : R) - (y : R)) < m) :
    HEq (ν.componentMk m x) (ν.componentMk n y) := by
  subst n
  apply heq_of_eq
  rw [ν.componentMk_eq_componentMk_iff]
  exact hxy

end MaxAddDegree
end
