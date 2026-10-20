public section

namespace TauCeti

open CliffordAlgebra

noncomputable section

/-- The unit direction from the antipode of the last coordinate vector toward an ambient vector.
At the excluded antipode it is totalized to zero by the real inverse. -/
noncomputable def realCliffordSpinLastLocalSectionDirection {n : ℕ}
    (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  (Real.sqrt (realCliffordForm (n + 1) 0 (Pi.single (Fin.last n) 1 - -x)))⁻¹ •
    (Pi.single (Fin.last n) 1 - -x)

end
end TauCeti
end
