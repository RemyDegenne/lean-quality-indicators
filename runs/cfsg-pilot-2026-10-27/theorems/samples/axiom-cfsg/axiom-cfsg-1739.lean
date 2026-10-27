public section

namespace CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K]

theorem eq_bot_or_eq_top_of_d8Invariant (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (B : Subgroup (D8Mod p K))
    (hB : ∀ (w : DihedralGroup 4), ∀ d ∈ B, d8Act w d ∈ B) : B = ⊥ ∨ B = ⊤ := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have : Fact p.Prime := ⟨hp⟩
  have hμ : Nat.card (rootsOfUnity p K) = p := card_rootsOfUnity_eq' hp.pos hζ
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨d, hdB⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hy : ∃ y : rootsOfUnity p K, y ≠ 1 ∧ ((1 : rootsOfUnity p K), y) ∈ B := by
    by_cases hb : d.2 = 1
    · have ha : d.1 ≠ 1 := fun ha => hd1' (Prod.ext ha hb)
      refine ⟨d.1⁻¹, inv_ne_one.mpr ha, ?_⟩
      have := hB (DihedralGroup.r 1) d hdB
      rw [d8Act_r_one, hb] at this
      exact this
    · refine ⟨d.2 * d.2, fun h => hb (eq_one_of_sq_eq_one_of_odd hpodd (by rwa [pow_two])), ?_⟩
      have h1 := hB (DihedralGroup.sr 0) d hdB
      rw [d8Act_sr_zero] at h1
      have h2 := B.mul_mem hdB h1
      have : d * (d.1⁻¹, d.2) = ((1 : rootsOfUnity p K), d.2 * d.2) :=
        Prod.ext (mul_inv_cancel _) rfl
      rwa [this] at h2
  obtain ⟨y, hy1, hyB⟩ := hy
  have hline : ∀ z : rootsOfUnity p K, ((1 : rootsOfUnity p K), z) ∈ B := by
    intro z
    obtain ⟨k, rfl⟩ := mem_zpowers_of_prime_card hμ hy1 (g' := z)
    have : ((1 : rootsOfUnity p K), y ^ k) = ((1 : rootsOfUnity p K), y) ^ k := by
      ext <;> simp
    rw [this]
    exact B.zpow_mem hyB k
  have hline' : ∀ z : rootsOfUnity p K, (z, (1 : rootsOfUnity p K)) ∈ B := by
    intro z
    have := hB (DihedralGroup.r 1) _ (hline z)
    rw [d8Act_r_one] at this
    simpa using this
  rw [eq_top_iff]
  intro d _
  have : d = (d.1, 1) * (1, d.2) := Prod.ext (mul_one _).symm (one_mul _).symm
  rw [this]
  exact B.mul_mem (hline' _) (hline _)

end CFSG.RankThree.PartOne.KFU
end
