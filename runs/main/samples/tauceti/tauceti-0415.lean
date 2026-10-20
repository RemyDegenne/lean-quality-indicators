public section

namespace TauCeti

namespace CliffordAlgebra

open _root_.CliffordAlgebra

noncomputable section

theorem isEmbedding_realCliffordSpinToUnits (n : ℕ) :
    Topology.IsEmbedding
      (spinGroup.toUnits (Q := realCliffordForm n 0)) := by
  have hcontinuous : Continuous
      (spinGroup.toUnits (Q := realCliffordForm n 0)) := by
    apply Units.continuous_iff.mpr
    exact ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  exact (hcontinuous.isClosedEmbedding
    (spinGroup.toUnits_injective (Q := realCliffordForm n 0))).isEmbedding

end
end CliffordAlgebra
end TauCeti
end
