public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.QuasithinUnique

theorem simpleInspection_sporadicList
    (hS : SporadicAutInner) : SimpleInspection SporadicList := by
  intro K _ _ β h hz ⟨s, hs, ⟨e⟩⟩
  by_cases hs1 : s = .J1
  · exfalso
    subst hs1
    obtain ⟨l, hl⟩ := isInnerAut_of_carrierJ1 e β
    obtain ⟨hl1, hll⟩ := h.involution_of_inner hz hl
    exact j1_involution_centralizer K ⟨e⟩ l hl1 hll
      (by rw [← fixedSubgroup_eq_centralizer hl]; exact h.charTwo)
  · have hβ : IsInnerAut β := hS s hs hs1 K ⟨e⟩ β h.involutory h.sylow
    have hs' : IsLemma115SporadicName s := by
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hs1 | simp [IsLemma115SporadicName]
    have hpc : CFSG.pCore 2 K = ⊥ := h.pCore_eq_bot hz
    let e' : (K ⧸ CFSG.pCore 2 K) ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨s, hs', ⟨e'.trans e⟩⟩,
      h.isTwoCentralInnerAut_of_inner hβ⟩))))

end CFSG.QuasithinUnique.Ch1
end
