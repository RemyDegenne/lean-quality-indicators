public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem exists_mem_le_sup_commuting (h : Hyp G R) {B X D T : Subgroup G} (hB : B ∈ R)
    (hXB : X ∈ lambdaSet R B) (hD : D ∈ R) (hBD : B ∈ lambdaSet R D)
    (hXD : X ∈ lambdaSet R D) (hT : T ∈ R) (hTD : T ∈ lambdaSet R D)
    (hXT : ¬ Commuting X T) : ∃ Z ∈ R, Z ≤ B ⊔ X ∧ Commuting Z T := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_cases hBT : Commuting B T
  · exact ⟨B, hB, le_sup_left, hBT⟩
  have hXR : X ∈ R := hXB.1.1
  have hcommD : ⁅M R D, M R D⁆ = D := (Q_eq_M h hD).2.2.1
  have hMD : IsPGroup 2 ↥(M R D) := (isPGroup_M hR hD).1
  have hTM : T ≤ M R D := QD.le_M hTD
  have hlineM : B ⊔ X ≤ M R D := sup_le (QD.le_M hBD) (QD.le_M hXD)
  have hBTne : B ≠ T := fun e => hBT (e ▸ hR.commuting_self hB)
  have hsBT : Special R B T := by
    rcases hR.rel B hB T hT hBTne with hc | ho | hs
    · exact absurd hc hBT
    · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hB hT
        (hMD.to_le (sup_le (QD.le_M hBD) hTM)))
    · exact hs
  have hBTD : ⁅B, T⁆ = D := QD.eq_of_le_of_mem hR hiso hsBT.1 hD
    (hcommD ▸ Subgroup.commutator_mono (QD.le_M hBD) hTM)
  obtain ⟨t, ht, ht1⟩ := hR.exists_ne_one hT
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hXR
  have hxt : ⁅x, t⁆ ∈ ⁅B, T⁆ := by
    rw [hBTD, ← hcommD]
    exact Subgroup.commutator_mem_commutator (QD.le_M hXD hx) (hTM ht)
  obtain ⟨b, hb, hbt⟩ := (bijOn_commutator_left hR hiso hB hT hsBT ht ht1).surjOn hxt
  replace hbt : ⁅b, t⁆ = ⁅x, t⁆ := hbt
  set y := b * x with hy
  have hyt : ⁅y, t⁆ = 1 := by
    have hxtD : ⁅x, t⁆ ∈ D := hBTD ▸ hxt
    have hcomm : b * ⁅x, t⁆ * b⁻¹ = ⁅x, t⁆ := by
      rw [(hBD.1.2.2 _ hxtD b hb).symm.eq, mul_inv_cancel_right]
    rw [hy, commutatorElement_mul_left_eq_conj_mul, hcomm]
    change ⁅x, t⁆ * ⁅b, t⁆ = 1
    rw [hbt]
    exact hR.mul_self D hD _ hxtD
  have hy1 : y ≠ 1 := by
    intro hy1
    have hxb : x = b⁻¹ := eq_inv_of_mul_eq_one_right hy1
    have hxB : x ∈ B ⊓ X := ⟨hxb ▸ B.inv_mem hb, hx⟩
    rw [inf_eq_bot hR hiso hB hXR hXB.1.2.1.symm, Subgroup.mem_bot] at hxB
    exact hx1 hxB
  have hyle : y ∈ B ⊔ X := Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right hx)
  obtain ⟨Z, hZ, hZle, hyZ⟩ := hXB.2 y hyle hy1
  refine ⟨Z, hZ, hZle, ?_⟩
  have hZT : Z ≠ T := by
    rintro rfl
    exact hBT ((Commuting.sup_right (hR.commuting_self hB) hXB.1.2.2).mono le_rfl hZle)
  rcases hR.rel Z hZ T hT hZT with hc | ho | hs
  · exact hc
  · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hZ hT
      (hMD.to_le (sup_le (hZle.trans hlineM) hTM)))
  · exfalso
    have hinj := (bijOn_commutator hR hiso hZ hT hs hyZ hy1).injOn
    exact ht1 (hinj ht T.one_mem (show ⁅y, t⁆ = ⁅y, 1⁆ by rw [hyt, commutatorElement_one_right]))

end CFSG.Timmesfeld.ARS
end
