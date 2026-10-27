public section

noncomputable section

open Set

namespace TauCeti

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {L φ : E → ℝ} {t h : ℝ}

/-- The *Hopf–Lax value* `inf_y (φ y + t L (t⁻¹ (x - y)))` of the initial datum `φ` for the
Lagrangian `L` at time `t` and position `x`. The infimum is taken in `ℝ`; it is the honest infimum
when `φ` and `L` are bounded below and `t ≥ 0`. -/
def hopfLax (L φ : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  ⨅ y, φ y + t * L (t⁻¹ • (x - y))

end Module
end TauCeti
end
end
