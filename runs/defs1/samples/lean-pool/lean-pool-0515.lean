@[expose] public section

noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

/-- The second half-lattice value `e₂ = ℘(ω₂/2)` (paper `pstrichprod`). -/
def e₂ : ℂ := ℘[L] (L.ω₂ / 2)

end PeriodPair
end
end
