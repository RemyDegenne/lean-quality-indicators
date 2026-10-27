public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair

open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP

open scoped Pointwise commutatorElement

section Geometry

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

theorem ctd_conj_le_K (hs : SPLSetup D.toSPLNot0) {c : G} (hc : c * D.z * c⁻¹ = D.t * D.z) :
    ∀ i ∈ D.Ict, c⁻¹ * i * c ∈ D.K₁ ⊔ D.K₂ := by
  have hzt := z_comm_t' D hs
  have hz2 : orderOf D.z = 2 := hs.syl.z_inv
  have hzw : D.z ∈ centralizer ({D.t * D.z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc D.z * (D.t * D.z) = D.z * D.t * D.z := (mul_assoc _ _ _).symm
      _ = D.t * D.z * D.z := by rw [hzt]
  have hCC : centralizer ({D.z} : Set G) ⊓ centralizer ({D.t * D.z} : Set G) = D.C ⊓ D.Ct := by
    ext x
    constructor
    · rintro ⟨hxz, hxw⟩
      have h1 : x * D.z = D.z * x := mem_centralizer_singleton_iff.mp hxz
      have h3 : x * (D.t * D.z) = D.t * D.z * x := mem_centralizer_singleton_iff.mp hxw
      refine ⟨hxz, mem_centralizer_singleton_iff.mpr ?_⟩
      have h4 : x * D.t * D.z = D.t * x * D.z := by
        calc x * D.t * D.z = x * (D.t * D.z) := mul_assoc _ _ _
          _ = D.t * D.z * x := h3
          _ = D.t * (D.z * x) := mul_assoc _ _ _
          _ = D.t * (x * D.z) := by rw [← h1]
          _ = D.t * x * D.z := (mul_assoc _ _ _).symm
      exact mul_right_cancel h4
    · rintro ⟨hxz, hxt⟩
      have h1 : x * D.z = D.z * x := mem_centralizer_singleton_iff.mp hxz
      have h2 : x * D.t = D.t * x := mem_centralizer_singleton_iff.mp hxt
      refine ⟨hxz, mem_centralizer_singleton_iff.mpr ?_⟩
      calc x * (D.t * D.z) = x * D.t * D.z := (mul_assoc _ _ _).symm
        _ = D.t * x * D.z := by rw [h2]
        _ = D.t * (x * D.z) := mul_assoc _ _ _
        _ = D.t * (D.z * x) := by rw [h1]
        _ = D.t * D.z * x := (mul_assoc _ _ _).symm
  have hΛ : IsPCompIn 2 (centralizer ({D.z} : Set G) ⊓ centralizer ({D.t * D.z} : Set G)) D.Ict := by
    rw [hCC]
    exact I_comp D hs
  have hbal := CFSG.GH74.GLS.Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf hz2 hzw hΛ
  have hCt : centralizer ({D.t * D.z} : Set G) =
      Stage1.Thm3.Sec4.cmap c (centralizer ({D.z} : Set G)) := by
    rw [← hc]
    exact (CFSG.GH74.GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj D.z c).symm
  have hpl : pLayerOf 2 (centralizer ({D.t * D.z} : Set G)) =
      Stage1.Thm3.Sec4.cmap c (D.K₁ ⊔ D.K₂) := by
    rw [hCt, Stage1.Thm3.Sec4.pLayerOf_cmap c, hs.comps.pLayerOf_eq]
  intro i hi
  have h := hbal hi
  rw [hpl] at h
  exact Stage1.Thm3.Sec4.mem_cmap.mp h

end Geometry
end CFSG.GH74.GLS.SP.Local
end
