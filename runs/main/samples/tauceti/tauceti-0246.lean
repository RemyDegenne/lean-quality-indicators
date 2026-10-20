public section

namespace TauCeti

section LocallyFinite

open scoped Pointwise

variable {Γ T : Type*} [TopologicalSpace T] [SMul Γ T] [ProperlyDiscontinuousSMul Γ T]
  {S : Set T}

@[to_additive
]
theorem locallyFinite_smul_of_isCompact [WeaklyLocallyCompactSpace T] (hS : IsCompact S) :
    LocallyFinite fun γ : Γ ↦ γ • S := fun x ↦
  let ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  ⟨K, hKx, properlyDiscontinuousSMul_iff.1 ‹_› hS hK⟩

end LocallyFinite
end TauCeti
end
