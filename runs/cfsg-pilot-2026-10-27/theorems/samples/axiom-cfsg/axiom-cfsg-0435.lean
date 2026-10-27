public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {P : Type} [Group P] {p : ℕ}

namespace NSetting

variable [Finite P] {Q : Subgroup P} {a : P}

omit [Finite P] in
theorem conj_mul {g h : P} {u v : ℕ} (hg : g * a * g⁻¹ = a ^ u) (hh : h * a * h⁻¹ = a ^ v) :
    (g * h) * a * (g * h)⁻¹ = a ^ (u * v) := by
  have e : (g * h) * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by group
  rw [e, hh, ← conj_pow, hg, ← pow_mul]

end NSetting
end CFSG.GH74.Uniqueness.SU.SU1
end
