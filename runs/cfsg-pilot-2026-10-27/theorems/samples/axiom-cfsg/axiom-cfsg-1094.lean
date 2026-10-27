public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open

open scoped Pointwise

namespace AltConfig

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω} (C : AltConfig G Ω α β)

variable [Finite G]

variable [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mapsDir_i₁ {g : G} (hg : g ∈ twoPointNormalizer G Ω α β (C.D.L C.i₁)) :
    C.MapsDir g C.i₁ C.i₁ := by
  obtain ⟨hg', hN⟩ := mem_twoPointNormalizer.mp hg
  intro δ₁ δ₂ δ₁' δ₂' e₁ e₂
  rw [(Subtype.ext e₁ : δ₁' = twoPointElt hg' • δ₁), (Subtype.ext e₂ : δ₂' = twoPointElt hg' • δ₂)]
  exact (C.D.normalizer_L_preserves_fibres hN δ₁ δ₂).1

end AltConfig
end CFSG.Holt.H78
end
