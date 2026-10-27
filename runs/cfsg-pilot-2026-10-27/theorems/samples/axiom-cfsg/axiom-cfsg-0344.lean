public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.GroupTheory

open scoped commutatorElement

namespace Sec10XSteps

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem card_closure_e_d (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) {e : G} (he : e ∈ Subgroup.closure ({a, c} : Set G))
    (hec : e ∉ Subgroup.zpowers c) : Nat.card (Subgroup.closure ({e, d} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hAcl : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  have hacA := Sec10XProof.closure_a_c_le h
  have heA : e ∈ A := hacA he
  have he3 : e ^ 3 = 1 := h.pow_three heA
  have he1 : e ≠ 1 := fun h1 => hec (h1 ▸ Subgroup.one_mem _)
  have hcl : Subgroup.closure ({e, d} : Set G) = Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hN : Subgroup.zpowers d ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) :
      Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (h.comm heA hdA) k).eq
  have hde : d ∉ Subgroup.zpowers e := by
    intro hd
    have hdac : d ∈ Subgroup.closure ({a, c} : Set G) := Subgroup.zpowers_le.mpr he hd
    have hAle : A ≤ Subgroup.closure ({a, c} : Set G) := by
      rw [hAcl, Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl | hy
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hdac
    have := Subgroup.card_le_of_le hAle
    rw [h.card_eq, Sec10XProof.card_closure_a_c h] at this
    norm_num at this
  rw [hcl, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
    (disjoint_zpowers_of_pow_three (h.pow_three hdA) hde), Nat.card_zpowers,
    Nat.card_zpowers, orderOf_eq_prime he3 he1, hd3]

end Sec10XSteps
end CFSG.RankThree.PartTwo.Sec10
end
