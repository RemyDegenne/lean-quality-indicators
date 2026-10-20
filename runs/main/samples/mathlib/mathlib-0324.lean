@[expose] public section

noncomputable section

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

@[simp]
theorem taylor_pow (n : ℕ) : taylor r (f ^ n) = taylor r f ^ n :=
  (taylorAlgHom r).map_pow ..

end CommSemiring
end Polynomial
end
end
