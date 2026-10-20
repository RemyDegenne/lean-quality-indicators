@[expose] public section

noncomputable section

open Homogenization MeasureTheory Set

namespace AVenhance.Infra.Section4

open AVenhance.Infra.Flow

/-- An open time neighborhood strictly containing every actual source
cutoff support, including its endpoints. -/
def amnrSourceFlowDomain {β : ℝ} (I : AVenhance.Ingredients β) (m : ℕ) (l : ℤ) : Set AmnrSpace :=
  {z | |z.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m| <
    (2 : ℝ) ^ (-24 : ℤ) * (AVenhance.a β I.Λ (m - 1))⁻¹}

end AVenhance.Infra.Section4
end
end
