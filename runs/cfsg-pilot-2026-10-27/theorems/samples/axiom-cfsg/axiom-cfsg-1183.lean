public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.OmGen

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

section Counting

variable {G : Type} [Group G]

open scoped Pointwise in
theorem exists_conj_le_of_card [Finite G] {C S R : Subgroup G} (hS : S ≤ C) (hR : R ≤ C)
    (hR2 : IsPGroup 2 R) {k m : ℕ} (hSc : Nat.card S = 2 ^ k)
    (hCc : Nat.card C ∣ 2 ^ k * m) (hm : Odd m) : ∃ h ∈ C, conjSub h R ≤ S := by
  have hSp : IsPGroup 2 S := IsPGroup.iff_card.2 ⟨k, hSc⟩
  have hSp' : IsPGroup 2 (S.subgroupOf C) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  have hRp' : IsPGroup 2 (R.subgroupOf C) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hR).symm
  have hidx : ¬ 2 ∣ (S.subgroupOf C).index := by
    have e := Subgroup.relIndex_mul_card S C
    rw [inf_of_le_left hS, hSc] at e
    have hd : S.relIndex C ∣ m := by
      refine (Nat.mul_dvd_mul_iff_right (by positivity : 0 < 2 ^ k)).1 ?_
      rw [e, mul_comm m]
      exact hCc
    have h1 := Nat.odd_iff.1 (hm.of_dvd_nat hd)
    intro h2
    have h2' : 2 ∣ S.relIndex C := h2
    omega
  let Q₀ : Sylow 2 C := hSp'.toSylow hidx
  obtain ⟨Q₁, hQ₁⟩ := hRp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q₁ Q₀
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  have hr' : (⟨r, hR hr⟩ : C) ∈ (Q₁ : Subgroup C) := hQ₁ (Subgroup.mem_subgroupOf.2 hr)
  have h1 : MulAut.conj g • (⟨r, hR hr⟩ : C) ∈ MulAut.conj g • (Q₁ : Subgroup C) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hr'
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  have h2 : (g * ⟨r, hR hr⟩ * g⁻¹ : C) ∈ (Q₀ : Subgroup C) := h1
  have h3 : (g * ⟨r, hR hr⟩ * g⁻¹ : C) ∈ S.subgroupOf C := h2
  exact h3

end Counting
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.OmGen
end
