public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_index_two_of_unique_of_quotient {M G₀ : Subgroup G}
    [(G₀.subgroupOf M).Normal] {t : G} (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) {x : G}
    (hxM : x ∈ M) {a : ℕ} (ha : 1 ≤ a) (hxo : orderOf x = 2 ^ a)
    (hxQ : orderOf (QuotientGroup.mk' (G₀.subgroupOf M) ⟨x, hxM⟩) = 2 ^ a)
    (hQ : ¬ 2 ^ (a + 1) ∣ Nat.card (M ⧸ G₀.subgroupOf M)) {n : ℕ} (hpow : IsConj t (x ^ n)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  obtain ⟨R, hRidx, hxR, hR⟩ := exists_index_two_of_orderOf_eq_two_pow ha hxQ hQ
  set Y := (R.comap (QuotientGroup.mk' (G₀.subgroupOf M))).map M.subtype with hY
  have hYM : Y ≤ M := map_subtype_le _
  have hmemY : ∀ y (hy : y ∈ M), y ∈ Y ↔ QuotientGroup.mk' (G₀.subgroupOf M) ⟨y, hy⟩ ∈ R := by
    intro y hy
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro h
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hYidx : Y.relIndex M = 2 := by
    rw [relIndex, hY, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective,
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hRidx]
  refine exists_normal_index_two_of_unique_of_relIndex_eq_two hYM hYidx huniq hxM
    (fun h => hxR ((hmemY x hxM).1 h)) hxo (fun y hy hyY _ => ?_) hpow
  have h1 := hR _ (fun h => hyY ((hmemY y hy).2 h))
  have h2 : orderOf (QuotientGroup.mk' (G₀.subgroupOf M) ⟨y, hy⟩) ∣ orderOf y := by
    rw [← orderOf_mk y hy]
    exact orderOf_map_dvd _ _
  rw [hxo]
  exact Nat.le_of_dvd (orderOf_pos y) (h1.trans h2)

end CFSG.SeitzReduction.F4Pilot
end
