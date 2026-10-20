@[expose] public section

namespace PowerSeries

theorem isUnit_artinHasseExp (p : ℕ) : IsUnit (artinHasseExp p) := by
  exact isUnit_iff_constantCoeff.mpr (by simp)

end PowerSeries
end
