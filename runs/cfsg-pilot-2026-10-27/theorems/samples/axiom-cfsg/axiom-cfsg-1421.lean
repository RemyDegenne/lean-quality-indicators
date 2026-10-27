public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof152ConfA

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_theta
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A)
    {Q : Subgroup G} (hQ : Q ∈ collectionIn (scriptQ A LB) X) :
    Q ⊓ Subgroup.centralizer (A : Set G) ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hX60
  obtain ⟨x, hxA, hxX, hx3, -, hxθ⟩ := exists_mem_inf_not_mem_theta hctx hAF hA
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hx1 : π ⟨x, hxX⟩ ≠ 1 := fun h => hxθ ⟨_, (QuotientGroup.eq_one_iff _).mp h, rfl⟩
  have hx3' : (π ⟨x, hxX⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
  intro y hy
  have hyX : y ∈ X := hQ.2 hy.1
  have hyx : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hy.2 x hxA).symm
  have hy3 : (π ⟨y, hyX⟩) ^ 3 = 1 := by
    refine pow_three_of_commute_of_mulEquiv e hx1 hx3' ?_
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyx
  have hyo : (π ⟨y, hyX⟩) ^ orderOf y = 1 := by
    rw [← map_pow]
    have : (⟨y, hyX⟩ : ↥X) ^ orderOf y = 1 := Subtype.ext (pow_orderOf_eq_one y)
    rw [this, map_one]
  have hcop : Nat.Coprime (orderOf y) 3 := by
    have h1 : orderOf y ∣ Nat.card Q := by
      have := orderOf_dvd_natCard (⟨y, hy.1⟩ : Q)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_left h1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3).symm
  have h1 : π ⟨y, hyX⟩ = 1 := by
    have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyo) (orderOf_dvd_of_pow_eq_one hy3)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact h2
  exact ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

end Proof152ConfA
end CFSG.RankThree.PartTwo.Sec15
end
