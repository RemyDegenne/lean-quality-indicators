namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_iff

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

p2m_open

namespace CerednikDrinfeld

namespace FormalOmega

namespace T3Aux

p2m_open

open TensorProduct

section Primitive

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}

theorem scaledE0_primIdx_not_div (hπ : Irreducible π) (M : FullLattice 𝒪 K) (A : ℕ)
    (hlow : algebraMap 𝒪 K (π ^ A) • (Pi.single 0 1 : Fin 2 → K) ∈ M.1)
    (hup : ∀ v ∈ M.1, ∀ i, IsLocalization.IsInteger 𝒪 (algebraMap 𝒪 K (π ^ A) * v i)) :
    ¬ ∃ w : ↥M.1, scaledE0 (K := K) π A (primIdx hπ M A hlow) = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  rintro ⟨w, hw⟩
  have hπK : algebraMap 𝒪 K π ≠ 0 := algebraMap_ne_zero' hπ
  by_cases h0 : primIdx hπ M A hlow = 0
  ·
    have hA : algebraMap 𝒪 K (π ^ A) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hπK
    have hw0 : algebraMap 𝒪 K (π ^ A) * (w : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ := by
      have h' := congrFun hw 0
      rw [h0, scaledE0, pow_zero, map_one, one_mul, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one, smul_eq_mul] at h'

      have hw' : (w : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K (π ^ A))⁻¹ := by
        calc (w : Fin 2 → K) 0 = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K π * (w : Fin 2 → K) 0) := by
              rw [← mul_assoc, inv_mul_cancel₀ hπK, one_mul]
          _ = (algebraMap 𝒪 K π)⁻¹ * (algebraMap 𝒪 K (π ^ A))⁻¹ := by rw [← h']
      rw [hw', mul_left_comm, mul_inv_cancel₀ hA, mul_one]
    obtain ⟨r, hr⟩ := hup w w.2 0
    rw [hw0] at hr
    have : algebraMap 𝒪 K (r * π) = 1 := by rw [map_mul, hr, inv_mul_cancel₀ hπK]
    have h1 : r * π = 1 := (IsFractionRing.injective 𝒪 K) (by rw [this, map_one])
    have hu : IsUnit (r * π) := by rw [h1]; exact isUnit_one
    exact hπ.not_isUnit (isUnit_of_mul_isUnit_right hu)
  ·
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero h0
    apply primIdx_min hπ M A hlow (show t < primIdx hπ M A hlow by omega)
    have : (w : Fin 2 → K) = scaledE0 (K := K) π A t := by
      apply smul_right_injective (Fin 2 → K) hπK
      show algebraMap 𝒪 K π • (w : Fin 2 → K) = algebraMap 𝒪 K π • scaledE0 (K := K) π A t
      rw [← hw, pi_smul_scaledE0_succ hπ, ht]
    rw [← this]; exact w.2

end Primitive
end T3Aux
end FormalOmega
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_iff
