namespace OAI

noncomputable section

namespace Rokhlin

namespace StrongUnitary

open MeasureTheory Filter Topology

open scoped Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SecondCountableTopology E]

lemma code_embedding : IsEmbedding (code : (E ≃ₗᵢ[ℂ] H) → ℕ → H) :=
  ⟨⟨rfl⟩, code_injective⟩

end StrongUnitary
end Rokhlin
end
end OAI
