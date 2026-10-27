public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG

variable {G : Type*} [Group G]

theorem commutator_inSubgroup_frattini_eq_bot [Finite G] {q : ℕ} (hq : q.Prime) {R A D : Subgroup G}
    (hRD : R ≤ normalizer (D : Set G)) (hAD : A ≤ normalizer (D : Set G)) (hRA : ⁅R, A⁆ = R)
    (hD : IsQDShape q D) : ⁅R, inSubgroup frattini D⁆ = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  rcases hD with ⟨hel, -⟩ | ⟨-, -, hcard, -, hfrat⟩
  · have hpg : Fact (IsPGroup q D) := ⟨IsElementaryAbelian.isPGroup q D⟩
    have : inSubgroup frattini D = ⊥ := by
      rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := q), Subgroup.map_bot]
    rw [this, Subgroup.commutator_bot_right]
  · rw [hfrat]
    have hcyc : IsCyclic (⁅D, D⁆ : Subgroup G) := isCyclic_of_prime_card hcard
    have hR : R ≤ normalizer ((⁅D, D⁆ : Subgroup G) : Set G) := fun r hr =>
      mem_normalizer_commutator (hRD hr) (hRD hr)
    have hA : A ≤ normalizer ((⁅D, D⁆ : Subgroup G) : Set G) := fun a ha =>
      mem_normalizer_commutator (hAD ha) (hAD ha)
    have h1 := commutator_le_centralizer_of_isCyclic hcyc hR hA
    rw [hRA] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1

end CFSG.RankThree.PartOne.Sec9Excl
end
