@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

open _root_.LinearMap

open Module (finrank)

variable {𝕜 E F F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']

theorem kyFanSum_add_le (k : ℕ) (A B : E →ₗ[𝕜] F) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := by
  have h := kyFanSum_add_le_square k (zeroExtension A) (zeroExtension B)
  simpa only [← zeroExtension_add, kyFanSum, singularValues_zeroExtension] using h

end TauCeti
end
