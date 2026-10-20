public section

namespace TauCeti.PowerSeries

open Filter

open scoped Topology

section Distinguished

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {c : ℝ} {s t : ℕ} {f : PowerSeries R}

theorem IsDistinguished.coeff_ne_zero (hf : IsDistinguished c s f) : f.coeff s ≠ 0 := by
  intro h
  have hpos := hf.gaussNorm_pos
  rw [← hf.norm_coeff_mul_pow_eq, h] at hpos
  simp at hpos

end SeminormedRing
end Distinguished
end TauCeti.PowerSeries
end
