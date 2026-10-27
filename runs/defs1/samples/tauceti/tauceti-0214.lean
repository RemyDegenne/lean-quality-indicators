public section

namespace TauCeti

namespace zHat

universe u

open Additive Multiplicative

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The `ℓ`-adic component of a profinite integer.** The projections of `Additive zHat` onto
the levels `ZMod (ℓ ^ k)` are compatible along the reduction maps, so the inverse-limit
universal property of `ℤ_[ℓ]` (`PadicInt.lift`) assembles them into a ring homomorphism
`Additive zHat →+* ℤ_[ℓ]`. It is characterized by `zHat.toZModPow_component`. -/
noncomputable def component : Additive zHat.{u} →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun k ↦ toZMod ⟨ℓ ^ k, pow_pos (Fact.out : ℓ.Prime).pos k⟩)
    fun k₁ k₂ hk ↦ castHom_comp_toZMod (m := ⟨ℓ ^ k₁, pow_pos (Fact.out : ℓ.Prime).pos k₁⟩)
      (n := ⟨ℓ ^ k₂, pow_pos (Fact.out : ℓ.Prime).pos k₂⟩) (pow_dvd_pow ℓ hk)

end zHat
end TauCeti
end
