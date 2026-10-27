public section

open Finset

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- Translate role-pair colors to the face-key convention indexed by the omitted coordinate. -/
def faceKey (k₀₁ k₀₂ k₁₂ : κ) : Fin 3 → κ := ![k₁₂, k₀₂, k₀₁]

end TauCeti
end
