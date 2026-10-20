public section

open Function Set Topology

open scoped ENNReal NNReal

namespace TauCeti

section NormedField

variable (𝕜 : Type*) [NormedField 𝕜]

/-- Finitely supported sequences, with the norm inherited from `ℓ²(ℕ, 𝕜)`. -/
noncomputable def finiteSupportL2 : Submodule 𝕜 (lp (fun _ : ℕ ↦ 𝕜) 2) :=
  (lpSubmodule 𝕜 (fun _ : ℕ ↦ 𝕜) 0).comap
    (lpSubmodule 𝕜 (fun _ : ℕ ↦ 𝕜) 2).subtype

end NormedField
end TauCeti
end
