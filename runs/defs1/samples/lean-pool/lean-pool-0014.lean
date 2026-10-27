@[expose] public section

namespace TauCeti

open InnerProductSpace Complex Filter Topology

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace OneParameterUnitaryGroup

variable [CompleteSpace H]

/-- The set of vectors at which the generator limit exists, as a `ℂ`-submodule. -/
-- `@[expose]` on this pair is deliberate and minimal. Consumers write `⟨x, hx⟩` for
-- elements of `(generator U).domain`, which typechecks only if the `domain` field
-- reduces to `generatorDomain U`; and `generator`'s own body projects `.choose` out of
-- that membership, so exposing one without the other does not elaborate. This is the
-- `api-design` carve-out for a consumer that must unfold, not blanket exposure.
def generatorDomain (U : OneParameterUnitaryGroup (H := H)) : Submodule ℂ H where
  carrier := {ψ | ∃ η, Tendsto (genDiffQuot U ψ) (𝓝[≠] 0) (𝓝 η)}
  add_mem' := by
    rintro a b ⟨ηa, ha⟩ ⟨ηb, hb⟩
    exact ⟨ηa + ηb, by rw [genDiffQuot_add]; exact ha.add hb⟩
  smul_mem' := by
    rintro c a ⟨ηa, ha⟩
    exact ⟨c • ηa, by rw [genDiffQuot_smul]; exact ha.const_smul c⟩
  zero_mem' := ⟨0, by rw [genDiffQuot_zero]; exact tendsto_const_nhds⟩

end OneParameterUnitaryGroup
end TauCeti
end
