public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

theorem mul_self_eq_one_of_isL2Natural_mod {K : Subgroup (MulAut W)} {C : Subgroup W} {m : ℕ}
    (h : E2.IsL2Natural K C m) {k : MulAut W} (hk : k ∈ K) {w : W} (hw : w ∈ commV K)
    (hwC : w ∉ C) (hkw : k w * w⁻¹ ∈ C) : k * k = 1 := by
  obtain ⟨hm, F, hF, hFt, hcard, e, β, -, hker, hβ⟩ := h
  have h2 : (2 : F) = 0 :=
    SecE.two_eq_zero_of_card hm (by rw [Nat.card_eq_fintype_card, hcard])
  have hd : k w * w⁻¹ ∈ commV K := Subgroup.subset_closure ⟨k, hk, w, rfl⟩
  have hkw' : k w ∈ commV K := by
    have := (commV K).mul_mem hd hw
    rwa [inv_mul_cancel_right] at this
  have hβw : Multiplicative.toAdd (β ⟨w, hw⟩) ≠ 0 := by
    intro h0
    have h1 : β ⟨w, hw⟩ = 1 := Multiplicative.toAdd.injective h0
    have hmem : (⟨w, hw⟩ : ↥(commV K)) ∈ β.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    exact hwC hmem.2
  have hβd : β ⟨k w * w⁻¹, hd⟩ = 1 := by
    have hmem : (⟨k w * w⁻¹, hd⟩ : ↥(commV K)) ∈ (commV K ⊓ C).subgroupOf (commV K) :=
      ⟨hd, hkw⟩
    rw [← hker] at hmem
    exact hmem
  have hβk : β ⟨k w, hkw'⟩ = β ⟨w, hw⟩ := by
    have e1 : (⟨k w, hkw'⟩ : ↥(commV K)) = ⟨k w * w⁻¹, hd⟩ * ⟨w, hw⟩ :=
      Subtype.ext (by simp)
    rw [e1, map_mul, hβd, one_mul]
  have hfix := hβ ⟨k, hk⟩ ⟨w, hw⟩ hkw'
  have e2 : (⟨((⟨k, hk⟩ : ↥K) : MulAut W) (w : W), hkw'⟩ : ↥(commV K)) = ⟨k w, hkw'⟩ := rfl
  rw [e2, hβk] at hfix
  have hsq := SecE.mul_self_eq_one_of_mulVec_eq h2 (e ⟨k, hk⟩).2 hβw hfix.symm
  have h3 : e (⟨k, hk⟩ * ⟨k, hk⟩) = 1 := by
    rw [map_mul]
    exact Subtype.ext hsq
  have h4 : (⟨k, hk⟩ * ⟨k, hk⟩ : ↥K) = 1 := e.injective (by rw [h3, map_one])
  exact congrArg Subtype.val h4

end C11AmS
end CFSG.Quasithin.Vol2.Ch10.SecB
end
