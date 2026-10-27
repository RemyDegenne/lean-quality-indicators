public section

namespace CFSG.Goldschmidt.Sec89

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem exists_orbitProd_mem (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hrank : CFSG.Open.pRank 2 (S : Subgroup G) ≤ 3) {x : G}
    (hxS : x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxC : x ∉ Subgroup.centralizer (A : Set G))
    (hx3 : ∀ s ∈ (S : Subgroup G), x⁻¹ * (x⁻¹ * (x⁻¹ * s * x) * x) * x = s)
    {N : Subgroup G} (hNS : N ≤ (S : Subgroup G))
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (N : Set G))
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hsq : ∀ s ∈ (S : Subgroup G), s ^ 2 ∈ N)
    (hfixN : ∀ c ∈ N, x⁻¹ * c * x = c → c = 1) :
    ∃ t ∈ (S : Subgroup G), t ^ 2 = 1 ∧ t ∉ A ∧ orbitProd x t ∈ N := by
  have hcomm := commutator_mem_of_sq_mem hsq
  obtain ⟨K, hK⟩ := exists_ker hNS hSN hxS hcomm
  have hKS : K ≤ (S : Subgroup G) := fun s hs => ((hK s).mp hs).1
  have hfix2 : ∀ c ∈ (S : Subgroup G), x⁻¹ * c * x = c → c ^ 2 = 1 := fun c hc hcx =>
    hfixN _ (hsq c hc) (by
      rw [pow_two]
      calc x⁻¹ * (c * c) * x = (x⁻¹ * c * x) * (x⁻¹ * c * x) := by group
        _ = c * c := by rw [hcx])
  obtain ⟨u, huS, hu2, hux, hu⟩ : ∃ u ∈ (S : Subgroup G), u ^ 2 = 1 ∧ x⁻¹ * u * x = u ∧
      ∀ c ∈ (S : Subgroup G), x⁻¹ * c * x = c → c = 1 ∨ c = u := by
    by_cases h : ∃ c ∈ (S : Subgroup G), c ≠ 1 ∧ x⁻¹ * c * x = c
    · obtain ⟨u, huS, hu1, hux⟩ := h
      refine ⟨u, huS, hfix2 u huS hux, hux, fun c hc hcx => ?_⟩
      by_contra hne
      push Not at hne
      have hcuS := (S : Subgroup G).mul_mem hc huS
      have hcux : x⁻¹ * (c * u) * x = c * u := by
        calc x⁻¹ * (c * u) * x = (x⁻¹ * c * x) * (x⁻¹ * u * x) := by group
          _ = c * u := by rw [hcx, hux]
      have hc2 := hfix2 c hc hcx
      have hu2 := hfix2 u huS hux
      have hcA : c ∉ A := fun h => hne.1 (eq_one_of_conj_eq hset h4 hxA hxC h hcx)
      have huA : u ∉ A := fun h => hu1 (eq_one_of_conj_eq hset h4 hxA hxC h hux)
      have hcuA : c * u ∉ A := fun h => by
        have h1 := eq_one_of_conj_eq hset h4 hxA hxC h hcux
        apply hne.2
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu2)
      exact hcuA (mul_mem_of_commute hset h4 hrank hc huS hc2 hu2
        (mul_comm_of_sq_eq_one hc2 hu2 (hfix2 _ hcuS hcux)) hcA huA)
    · push Not at h
      exact ⟨1, (S : Subgroup G).one_mem, one_pow 2, by group, fun c hc hcx =>
        Or.inl (by by_contra h1; exact h c hc h1 hcx)⟩
  have hF2 : ∀ s ∈ (S : Subgroup G), s ∈ K ∨ s * u ∈ K := by
    intro s hs
    have hmS := orbitProd_mem hxS hs
    have hyS : (x⁻¹ * s * x) * (x⁻¹ * (x⁻¹ * s * x) * x) ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem (conj_mem_of_mem_normalizer hxS hs)
        (conj_mem_of_mem_normalizer hxS (conj_mem_of_mem_normalizer hxS hs))
    have hmx : (orbitProd x s)⁻¹ * (x⁻¹ * orbitProd x s * x) ∈ N := by
      have h3 := hx3 s hs
      have e : (orbitProd x s)⁻¹ * (x⁻¹ * orbitProd x s * x) =
          ((x⁻¹ * s * x) * (x⁻¹ * (x⁻¹ * s * x) * x))⁻¹ * s⁻¹ *
            ((x⁻¹ * s * x) * (x⁻¹ * (x⁻¹ * s * x) * x)) *
              (x⁻¹ * (x⁻¹ * (x⁻¹ * s * x) * x) * x) := by
        simp only [orbitProd]; group
      rw [e, h3]
      exact hcomm _ hyS s hs
    obtain ⟨n, hn, hnx⟩ := exists_mul_conj_eq hxN hfixN hmx
    rcases hu _ ((S : Subgroup G).mul_mem hmS (hNS hn)) hnx with h | h
    · left
      refine (hK s).mpr ⟨hs, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h]
      exact N.inv_mem hn
    · right
      refine (hK _).mpr ⟨(S : Subgroup G).mul_mem hs huS, ?_⟩
      have hpu : orbitProd x u = u := by
        simp only [orbitProd, hux]
        rw [← pow_two, hu2, one_mul]
      have h2 := orbitProd_mul_mem hNS hSN hxS hcomm hs huS
      have e : orbitProd x s * orbitProd x u = orbitProd x s ^ 2 * n := by
        rw [hpu, ← h, pow_two, mul_assoc]
      rw [e] at h2
      have e2 : orbitProd x (s * u) = (orbitProd x s ^ 2 * n) *
          ((orbitProd x (s * u))⁻¹ * (orbitProd x s ^ 2 * n))⁻¹ := by group
      rw [e2]
      exact N.mul_mem (N.mul_mem (hsq _ hmS) hn) (N.inv_mem h2)
  by_cases huK : u ∈ K
  · obtain ⟨t, htS, ht2, htA⟩ := exists_sq_eq_one_not_mem hset h4
    have htK : t ∈ K := by
      rcases hF2 t htS with h | h
      · exact h
      · have := K.mul_mem h (K.inv_mem huK)
        simpa using this
    exact ⟨t, htS, ht2, htA, ((hK t).mp htK).2⟩
  · have hu1 : u ≠ 1 := fun h => huK (h ▸ K.one_mem)
    have hindex : K.relIndex (S : Subgroup G) = 2 := by
      show (K.subgroupOf (S : Subgroup G)).index = 2
      refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨u, huS⟩, ?_, fun b => ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact huK
      · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact (hF2 b b.2).symm
    have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
    obtain ⟨g, hg⟩ : ∃ g : G, g⁻¹ * u * g ∈ K := by
      by_contra hno
      push Not at hno
      obtain ⟨N₀, hN₀, hsq₀, huN₀⟩ :=
        Quasithin.thompson_transfer_exists_normal S hKS hindex hord hno
      have := hset.isSimpleGroup
      rcases Subgroup.Normal.eq_bot_or_eq_top N₀ with h | h
      · obtain ⟨a, b, hab⟩ := hset.nonabelian
        have hsq1 : ∀ g : G, g * g = 1 := fun g => by
          have := hsq₀ g
          rwa [h, Subgroup.mem_bot, pow_two] at this
        apply hab
        calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq1 _)).symm
          _ = b * a := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq1 b),
              inv_eq_of_mul_eq_one_right (hsq1 a)]
      · exact huN₀ (h ▸ Subgroup.mem_top u)
    refine ⟨g⁻¹ * u * g, hKS hg, conj_sq_eq_one hu2, fun htA => ?_, ((hK _).mp hg).2⟩
    have huA : u ∈ A := by
      have := hset.closed _ htA g⁻¹ (by simpa [mul_assoc] using huS)
      simpa [mul_assoc] using this
    exact hu1 (eq_one_of_conj_eq hset h4 hxA hxC huA hux)

end CFSG.Goldschmidt.Sec89
end
