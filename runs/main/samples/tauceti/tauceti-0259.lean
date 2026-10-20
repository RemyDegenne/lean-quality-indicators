public section

open WeierstrassCurve TauCeti.Isogeny

namespace TauCeti.WorkedExamples

variable (K : Type*) [Field K] [Finite K] [Algebra (ZMod 3) K]

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem isOrdinary_curveX3AddX : curveX3AddX.IsOrdinary 5 := by
  rw [← not_isSupersingular, isSupersingular_iff_dvd_frobeniusTrace, frobeniusTrace_curveX3AddX]
  decide

end TauCeti.WorkedExamples
end
