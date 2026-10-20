public section

open Set

namespace TauCeti

variable (𝕜 E F : Type*)

variable {𝕜 E F}

section Basic

variable {G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem banachMazurDist_of_isEmpty [IsEmpty (E ≃L[𝕜] F)] : banachMazurDist 𝕜 E F = 0 :=
  Real.iInf_of_isEmpty _

end Basic
end TauCeti
end
