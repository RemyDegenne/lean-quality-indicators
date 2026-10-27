public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open

open scoped Pointwise commutatorElement

section TwoPoint

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

theorem Sec4Setting.mem_longInv_iff_of_odd_twoPointKernel (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (hT : Odd (Nat.card (twoPointKernel G Ω α β)))
    (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) {y : G} (hy : orderOf y = 2) (hyαβ : y • α = β) :
    y ∈ longInv G Ω ↔ ∃! δ, δ ∈ holtDelta G Ω α β ∧ y • δ = δ := by
  constructor
  · intro hyJ
    obtain ⟨γ, hγ, huniq⟩ := hyJ.2
    exact ⟨γ, ⟨⟨y, ⟨hyJ, hyαβ⟩, hγ⟩, hγ⟩, fun δ hδ => huniq δ hδ.2⟩
  · rintro ⟨δ₀, ⟨hδ₀Δ, hδ₀⟩, huniq⟩
    have hyX := mem_stabilizer_pair_of_orderOf_eq_two hy hyαβ
    have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
    have hŷ : twoPointElt hyX ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
      rw [mem_longInv_subgroup_iff]
      have : Nontrivial (holtDelta G Ω α β) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      refine (mem_longInvAt_of_mul_self (δ := ⟨δ₀, hδ₀Δ⟩) ?_ (fun ε => ?_) (exists_ne _)).1
      · rw [← map_mul, show (⟨y, hyX⟩ : stabilizer G ({α, β} : Set Ω)) * ⟨y, hyX⟩ = 1 from
          Subtype.ext hyy, map_one]
      · rw [Equiv.Perm.smul_def, Subtype.ext_iff, Subtype.ext_iff]
        exact ⟨fun h => huniq _ ⟨ε.2, h⟩, fun h => by rw [coe_twoPointHom_apply, h]; exact hδ₀⟩
    obtain ⟨x, hx, hxy⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3 _).mp hŷ
    have hk : x⁻¹ * y ∈ twoPointKernel G Ω α β := by
      rw [mem_twoPointKernel]
      refine ⟨?_, ?_, fun δ hδ => ?_⟩
      · rw [mul_smul, hyαβ, inv_smul_eq_iff, hx.2]
      · rw [mul_smul, smul_eq_of_orderOf_eq_two hy hyαβ, inv_smul_eq_iff,
          smul_eq_of_mem_longInvSwap hx]
      · rw [mul_smul, inv_smul_eq_iff]
        exact hxy ⟨δ, hδ⟩
    have hodd : Odd (orderOf (x⁻¹ * y)) := Odd.of_dvd_nat hT (Subgroup.orderOf_dvd_natCard _ hk)
    obtain ⟨g, hg⟩ := exists_conj_eq_mul_of_odd (mul_self_eq_one_of_mem_longInv hx.1) hodd
      (by rw [mul_inv_cancel_left]; exact hyy)
    rw [mul_inv_cancel_left] at hg
    rw [← hg]
    exact conj_mem_longInv hx.1 g

end TwoPoint
end CFSG.Holt.H78
end
