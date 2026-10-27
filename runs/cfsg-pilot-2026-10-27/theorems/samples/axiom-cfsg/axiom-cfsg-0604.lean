public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2.KGNat

open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem autOn_le_normZH {L V X : Subgroup G} [IsMulCommutative ↥V]
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    autOn X V ≤ normZH (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) := by
  rintro _ ⟨⟨x, hxN⟩, hxX, rfl⟩
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := hXN ⟨hxX, hxN⟩
  have hxL' : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hxL
  refine ⟨fun z => ?_, fun h => ?_⟩
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change (z : G) ∈ _ ↔ ((conjAct V ⟨x, hxN⟩ z : ↥V) : G) ∈ _
    rw [conjAct_coe]
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro hz l hl
      have h1 := hz (x⁻¹ * l * x⁻¹⁻¹) ((Subgroup.mem_normalizer_iff.mp hxL' l).mp hl)
      calc l * (x * z * x⁻¹) = x * ((x⁻¹ * l * x⁻¹⁻¹) * z) * x⁻¹ := by group
        _ = x * (z * (x⁻¹ * l * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
        _ = x * z * x⁻¹ * l := by group
    · intro hz l hl
      have h1 := hz (x * l * x⁻¹) ((Subgroup.mem_normalizer_iff.mp hxL l).mp hl)
      calc l * (z : G) = x⁻¹ * ((x * l * x⁻¹) * (x * z * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * z * x⁻¹) * (x * l * x⁻¹)) * x := by rw [h1]
        _ = z * l := by group
  · constructor
    · rintro ⟨⟨l, hlN⟩, hlL, rfl⟩
      refine ⟨⟨x * l * x⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem hxN hlN)
        ((Subgroup.normalizer (V : Set G)).inv_mem hxN)⟩,
        (Subgroup.mem_normalizer_iff.mp hxL l).mp hlL, ?_⟩
      ext v
      simp only [MulAut.mul_apply, conjAct_coe]
      rw [← map_inv, conjAct_coe]
      simp only [Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    · rintro ⟨⟨l, hlN⟩, hlL, hl⟩
      refine ⟨⟨x⁻¹ * l * x⁻¹⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem ((Subgroup.normalizer (V : Set G)).inv_mem hxN)
          hlN) ((Subgroup.normalizer (V : Set G)).inv_mem
          ((Subgroup.normalizer (V : Set G)).inv_mem hxN))⟩,
        (Subgroup.mem_normalizer_iff.mp hxL' l).mp hlL, ?_⟩
      have h2 : h = (conjAct V ⟨x, hxN⟩)⁻¹ * conjAct V ⟨l, hlN⟩ * conjAct V ⟨x, hxN⟩ := by
        rw [hl]
        group
      rw [h2]
      ext v
      simp only [MulAut.mul_apply]
      rw [← map_inv]
      simp only [conjAct_coe, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
end
