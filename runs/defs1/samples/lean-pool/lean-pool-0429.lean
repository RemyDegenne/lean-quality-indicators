@[expose] public section

namespace ZetaZeros

/-- The odd part of the twisted pair, `hz = (fz z - fz (conj z)) / (2i)`. -/
@[zz_tag "def_h_z"]
noncomputable def hz (eta : ℝ → ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (fz eta z u - fz eta ((starRingEnd ℂ) z) u) / (2 * Complex.I)

end ZetaZeros
end
