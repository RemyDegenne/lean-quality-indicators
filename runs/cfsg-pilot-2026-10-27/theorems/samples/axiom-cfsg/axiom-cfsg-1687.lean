public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.SignalizerFunctorTheorem CFSG.Assembly.Dichotomy

open scoped commutatorElement

section Constancy

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem centralOddCore_le_normalizer_uCore {F : Subgroup G} (hFA : F ≤ A) :
    centralOddCore A ≤ Subgroup.normalizer (uCore F : Set G) := by
  intro t ht
  have htF : ∀ f ∈ F, t * f = f * t := fun f hf =>
    (Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer A ht) f (hFA hf)).symm
  have htF' : ∀ f ∈ F, t⁻¹ * f = f * t⁻¹ := fun f hf => by
    have := htF f hf
    calc t⁻¹ * f = t⁻¹ * (f * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * f) * t⁻¹ := by rw [this]
      _ = f * t⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_uCore htF hy, fun hy => ?_⟩
  have := conj_mem_uCore htF' hy
  simpa [mul_assoc] using this

end Constancy
end CFSG.ClassicalInvolution.Balance.Bootstrap
end
