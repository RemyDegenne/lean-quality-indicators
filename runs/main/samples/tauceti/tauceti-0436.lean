public section

open MeasureTheory Set TopologicalSpace

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}

section RelativelyCompactSubdomains

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  [LocallyCompactSpace X] [RegularSpace X] {f : X → ε} {Ω : Opens X}

theorem locallyIntegrableOn_iff_forall_isCompact_closure :
    LocallyIntegrableOn f Ω μ ↔
      ∀ V : Opens X, IsCompact (closure (V : Set X)) → closure (V : Set X) ⊆ Ω →
        LocallyIntegrableOn f V μ := by
  constructor
  · intro hf V _ hV
    exact hf.mono_set (subset_closure.trans hV)
  · intro h x hx
    obtain ⟨V, hVo, hxV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton Ω.isOpen
        (singleton_subset_iff.mpr hx)
    have hf := h ⟨V, hVo⟩ hVc hVΩ x (hxV (mem_singleton x))
    simp only [Opens.coe_mk, hVo.nhdsWithin_eq (hxV (mem_singleton x))] at hf
    exact hf.filter_mono nhdsWithin_le_nhds

end RelativelyCompactSubdomains
end TauCeti
end
