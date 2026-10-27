public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75 CFSG.Open

open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}
  [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

section Count

theorem ncard_delta_three (M : TModel T T₁ 3 m) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ 3 m) :
    (classD T ∩ (cfgM T T₁ : Set G)).ncard = (2 ^ m + 1) * ((2 ^ m) ^ 2 - 1) := by
  have := hc.finite
  have hcfg := hc.sec3.cfg
  rw [classD_inter_cfgM_eq_image hc, (mul_injOn_normIn hc).ncard_image]
  set S : Set (G × G) :=
    {p : G × G | p.1 ∈ normIn T T₁ ∧ p.2 ∈ normIn T₁ T ∧ p.1 * p.2 ∈ classD T} with hS
  have hSsplit : S = {p ∈ S | p.2 = 1} ∪ {p ∈ S | p.2 ≠ 1} := by
    ext p
    simp only [Set.mem_union, Set.mem_sep_iff]
    tauto
  have hdisj : Disjoint {p ∈ S | p.2 = 1} {p ∈ S | p.2 ≠ 1} := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  rw [hSsplit, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  have hLcard : ((normIn T T₁ : Set G)).ncard = (2 ^ m) ^ 2 := by
    rw [← Nat.card_coe_set_eq]
    exact card_normIn_three hc
  have hL₁card : ((normIn T₁ T : Set G)).ncard = (2 ^ m) ^ 2 := by
    rw [← Nat.card_coe_set_eq]
    exact card_normIn₁_three hc
  have h1 : {p ∈ S | p.2 = 1}.ncard = (2 ^ m) ^ 2 - 1 := by
    have hset : {p ∈ S | p.2 = 1} =
        (fun l : G => (l, (1 : G))) '' ((normIn T T₁ : Set G) \ ({1} : Set G)) := by
      ext ⟨l, e⟩
      simp only [hS, Set.mem_ofPred_eq, Set.mem_image, Set.mem_sdiff,
        SetLike.mem_coe, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hl, -, hD⟩, rfl⟩
        refine ⟨l, ⟨hl, ?_⟩, rfl, rfl⟩
        rintro rfl
        exact ne_one_of_mem_classD (by simpa using hD) rfl
      · rintro ⟨l', ⟨hl', hl'1⟩, rfl, rfl⟩
        exact ⟨⟨hl', (normIn T₁ T).one_mem, by
          simpa using mem_classD_of_mem (normIn_le _ _ hl') hl'1⟩, rfl⟩
    rw [hset, Set.ncard_image_of_injective _ (fun a b h => congrArg Prod.fst h),
      Set.ncard_sdiff_singleton_of_mem (normIn T T₁).one_mem, hLcard]
  have h2 : {p ∈ S | p.2 ≠ 1}.ncard = ((2 ^ m) ^ 2 - 1) * 2 ^ m := by
    have hmaps : ∀ p ∈ {p ∈ S | p.2 ≠ 1}, p.2 ∈ ((normIn T₁ T : Set G) \ ({1} : Set G)) := by
      rintro p ⟨⟨-, he, -⟩, hne⟩
      exact ⟨he, hne⟩
    have := ncard_eq_mul_of_fibres {p ∈ S | p.2 ≠ 1} ((normIn T₁ T : Set G) \ ({1} : Set G))
      Prod.snd hmaps (2 ^ m) (by
        rintro e ⟨he, he1⟩
        have he1' : e ≠ 1 := he1
        have hfib : {p : G × G | p ∈ {p ∈ S | p.2 ≠ 1} ∧ p.2 = e} =
            (fun l : G => (l, e)) '' {l : G | l ∈ normIn T T₁ ∧ l * e ∈ classD T} := by
          ext ⟨l, e'⟩
          simp only [hS, Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨⟨hl, -, hD⟩, -⟩, rfl⟩
            exact ⟨l, ⟨hl, hD⟩, rfl, rfl⟩
          · rintro ⟨l', ⟨hl', hD⟩, rfl, rfl⟩
            exact ⟨⟨⟨hl', he, hD⟩, he1'⟩, rfl⟩
        have hcomm : {l : G | l ∈ normIn T T₁ ∧ l * e ∈ classD T} =
            {l : G | l ∈ normIn T T₁ ∧ e * l ∈ classD T} := by
          ext l
          simp only [Set.mem_ofPred_eq]
          constructor
          · rintro ⟨hl, hD⟩
            exact ⟨hl, by rwa [← hcfg.comm_L_L₁ hl he]⟩
          · rintro ⟨hl, hD⟩
            exact ⟨hl, by rwa [hcfg.comm_L_L₁ hl he]⟩
        rw [hfib, Set.ncard_image_of_injective _ (fun a b h => congrArg Prod.fst h), hcomm]
        exact ncard_mul_mem_D M h62 h63 hc he he1')
    rw [this, Set.ncard_sdiff_singleton_of_mem (normIn T₁ T).one_mem, hL₁card]
  rw [h1, h2]
  ring_nf

end Count
end CFSG.CGT.T75F
end
