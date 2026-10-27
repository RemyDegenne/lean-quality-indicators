public section

noncomputable section

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace RayClassCharacter

variable {𝔪 𝔫 : Modulus K}

/-- A ray class character is primitive if it is not induced from a strictly smaller modulus. -/
def IsPrimitive (χ : RayClassCharacter 𝔪) : Prop :=
  ∀ (𝔫 : Modulus K) (h : 𝔫 ∣ 𝔪) (ψ : RayClassCharacter 𝔫),
    ψ.induced h = χ → 𝔫 = 𝔪

end RayClassCharacter
end TauCeti.GlobalNumberFields
end
end
