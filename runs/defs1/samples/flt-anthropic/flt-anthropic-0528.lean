namespace P2MW.S_NumberField_PlaceDecomp_exists_faithful_bridge_isBase_isLocalFundamentalClass

attribute [-instance] ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 1600000

p2m_open

p2m_open_scoped

set_option linter.unusedSectionVars false

namespace NumberField

namespace PlaceDecomp

namespace FCFamily3b

p2m_open

structure BridgeFC (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) where
  q : ℕ
  [hq : Fact q.Prime]
  L : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd : FiniteDimensional ℚ_[q] L]
  [act : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L]
  [faith : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F w)) L]
  [actU : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ]
  Φ : w.adicCompletion F ≃+* L
  h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x
  h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)
  h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x
  hqw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal
  K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd₀ : FiniteDimensional ℚ_[q] K₀]
  base : ExtCitation.LocalLevel.IsBase q L (↥(NumberField.PlaceDecomp.decomp E F w)) K₀
  θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ
  hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : L)
  u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ)
  hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u

end FCFamily3b
end PlaceDecomp
end NumberField
end P2MW.S_NumberField_PlaceDecomp_exists_faithful_bridge_isBase_isLocalFundamentalClass
