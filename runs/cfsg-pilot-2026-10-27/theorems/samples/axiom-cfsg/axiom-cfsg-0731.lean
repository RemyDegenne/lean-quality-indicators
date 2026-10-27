public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin OrthBlk
  CFSG.Open

open CFSG.RankThree.Classical2 (orthDerived)

namespace B3Data

variable {K : Type} [Field K] (X : B3Data K)

theorem coe_conjσ (g : elementaryGroup (quadOdd 3 K)) :
    (X.conjσ g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) =
      X.σ * g * X.σ⁻¹ := rfl

end B3Data
end CFSG.LieType.SeitzGeneration
end
