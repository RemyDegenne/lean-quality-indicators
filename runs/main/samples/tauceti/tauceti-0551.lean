public section

namespace TauCeti.FiniteQuadraticModule

section

variable (k : ℕ) [NeZero k] (θ : ℤ)

@[simp]
theorem dyadicCyclic_quadratic_intCast (j : ℤ) :
    (dyadicCyclic k θ).quadratic (j : ZMod (2 ^ k)) =
      ((θ * j ^ 2 / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) := by
  unfold dyadicCyclic
  rw [cyclic_quadratic, cyclicMap_intCast, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  push_cast
  ring_nf

end
end TauCeti.FiniteQuadraticModule
end
