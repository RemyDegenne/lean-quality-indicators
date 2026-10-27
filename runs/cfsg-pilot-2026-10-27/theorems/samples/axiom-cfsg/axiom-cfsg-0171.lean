public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.GF2Type.Smith1979W3.Cert690

variable {G : Type} [Group G] [Finite G] (S : Setting G) (L : S.Qt ≃ₗ[ZMod 2] V₀)

theorem pgl_eq_z_of_commute (hF : PGLFactsProp) [IsSimpleGroup G] (hw : S.width = 3)
    (h336 : Nat.card S.Mbar = 336) (hL : ∀ v, qModel false (L v) = S.q v)
    (hK : mbarModel S L = KPGL) :
    ∀ y : S.M, S.ρ y ∉ pglM0 S L → ∀ e ∈ S.QG, IsConj e S.z →
      e * (y : G) = (y : G) * e → e = S.z := by
  unfold PGLFactsProp at hF
  obtain ⟨-, -, -, -, -, -, hdisj, -, -, hswap, -, -, hnocensus, -, -, -⟩ := hF
  have hplus : QtPlusType S := qtPlusType_of_card S hw (Or.inl h336)
  have hminus : (false = true) ↔ ¬ QtPlusType S :=
    ⟨fun h => absurd h (by decide), fun h => absurd hplus h⟩
  intro y hy e heQ heconj hey
  by_contra hne
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_comm.mp heconj)
  have hgQ : g * S.z * g⁻¹ ∈ S.QG := hg.symm ▸ heQ
  have hgne : g * S.z * g⁻¹ ≠ S.z := by rw [hg]; exact hne
  obtain ⟨hb0, hbq, hcond⟩ := censusCond_conj S L false hw hL hminus hgQ hgne
  rw [hg] at hb0 hbq hcond
  have hcondK : CensusCond false KPGL
      (((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom) (L (S.cl e)) :=
    hK ▸ hcond
  have hbV : L (S.cl e) ∈ VPlus ∨ L (S.cl e) ∈ VStar := by
    by_contra h
    simp only [not_or] at h
    exact hnocensus (L (S.cl e)) hb0 hbq h.1 h.2 _ hcondK
  have hfix : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e := by
    rw [S.ρ_cl y heQ]
    have hye : (y : G) * e * (y : G)⁻¹ = e := by
      calc (y : G) * e * (y : G)⁻¹ = e * (y : G) * (y : G)⁻¹ := by rw [← hey]
        _ = e := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [hye]
  have hfixψ : conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (L (S.cl e)) =
      L (S.cl e) := by
    rw [conjL_apply, LinearEquiv.symm_apply_apply, hfix]
  have hmemK : conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ KPGL := by
    rw [← hK]
    exact conjL_ρ_mem_mbarModel S L y
  have hnotK : conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∉ KPGL0 := by
    intro h
    exact hy ((ρ_mem_pglM0_iff S L y).mpr h)
  obtain ⟨hVPlus, hVStar⟩ := hswap (conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    hmemK hnotK
  have hbPlus : L (S.cl e) ∈ VPlus := by
    rcases hbV with h | h
    · exact h
    · have h1 : (conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) (L (S.cl e)) ∈
          VStar.map ((conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
            V₀ →ₗ[ZMod 2] V₀) := Submodule.mem_map_of_mem h
      rw [hfixψ, hVStar] at h1
      exact h1
  have hbStar : L (S.cl e) ∈ VStar := by
    have h1 : (conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) (L (S.cl e)) ∈
        VPlus.map ((conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
          V₀ →ₗ[ZMod 2] V₀) := Submodule.mem_map_of_mem hbPlus
    rw [hfixψ, hVPlus] at h1
    exact h1
  have hbot : L (S.cl e) ∈ (⊥ : Submodule (ZMod 2) V₀) := by
    rw [← hdisj]
    exact ⟨hbPlus, hbStar⟩
  rw [Submodule.mem_bot] at hbot
  exact hb0 hbot

end CFSG.GF2Type.Smith1979W3
end
