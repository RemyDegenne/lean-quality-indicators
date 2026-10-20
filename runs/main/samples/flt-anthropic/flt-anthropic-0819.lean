namespace P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

p2m_open

namespace CerednikDrinfeld

namespace FormalOmega

namespace T2aAux

p2m_open

open TensorProduct

section Bounds

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

theorem exists_pow_isInteger (hπ : Irreducible π) (s : Finset K) :
    ∃ k : ℕ, ∀ c ∈ s, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ k) * c) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪) s id
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hπ
  refine ⟨k, fun c hc => ?_⟩
  have := hb c hc
  rw [id, Algebra.smul_def, hu, map_mul, mul_assoc] at this
  obtain ⟨r, hr⟩ := this
  refine ⟨↑u⁻¹ * r, ?_⟩
  rw [map_mul, hr, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

end Bounds
end T2aAux
end FormalOmega
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_toOmega_mem_upperHalfPlane
