public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open
  Matrix

section NOrbitsA0

theorem mem_orbN0_of_mem_A0 : ∀ a ∈ A0, a ≠ 1 →
    a ∈ orbN0 alpha ∨ a ∈ orbN0 pi12 ∨ a ∈ orbN0 pi3 ∨ a ∈ orbN0 rho28 := by
  intro a ha ha1
  obtain ⟨k, hk, hke⟩ := exists_lt_of_mem_A0 ha
  rcases orbCheck_spec.2.2.2.2.2.2 k hk with h | h
  · exact absurd (code_injective (by rw [code_one, ← hke, h])) ha1
  · rw [hke] at h
    have hmem : ∀ {x : List ℕ} {cs : List (List ℕ)}, (∀ i ∈ x, i < 12) →
        (∀ c ∈ cs, ∀ i ∈ c, i < 12) → code a ∈ orbCodes x cs → a ∈ orbElems x cs := by
      intro x cs hx hcs hc
      rw [← map_code_orbElems hx hcs] at hc
      obtain ⟨z, hz, hze⟩ := List.mem_map.mp hc
      rwa [← code_injective hze]
    rw [orbN0_alpha, orbN0_pi12, orbN0_pi3, orbN0_rho28]
    simp only [List.mem_append] at h
    simp only [Set.mem_setOf_eq]
    rcases h with ((h | h) | h) | h
    · exact Or.inl (hmem (by decide) (orbWords_lt (Or.inl rfl)) h)
    · exact Or.inr (Or.inl (hmem (by decide) (orbWords_lt (Or.inr (Or.inl rfl))) h))
    · exact Or.inr (Or.inr (Or.inl
        (hmem (by decide) (orbWords_lt (Or.inr (Or.inr (Or.inl rfl)))) h)))
    · exact Or.inr (Or.inr (Or.inr
        (hmem (by decide) (orbWords_lt (Or.inr (Or.inr (Or.inr rfl)))) h)))

end NOrbitsA0
end CFSG.ClassicalInvolution.Sp62Rec
end
