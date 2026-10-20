public section

namespace QuadraticAlgebra

variable {R : Type*}

section discr

theorem discr_intCast [CommRing R] (a b : ℤ) : discr (a : R) (b : R) = discr a b := by
  simp [discr_def]

end discr
end QuadraticAlgebra
end
