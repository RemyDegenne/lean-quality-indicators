public section

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open Subgroup CFSG.Sporadic.SuzOddCore

section Identities

variable {P : Type*} [Group P]

theorem conj_conj_of_mul_self {t h : P} (ht : t * t = 1) : t * (t * h * t⁻¹) * t⁻¹ = h := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [hti, ← mul_assoc, ← mul_assoc, ht, one_mul, mul_assoc, ht, mul_one]

end Identities
end CFSG.Sporadic.SuzRecog.B0Gluing
end
