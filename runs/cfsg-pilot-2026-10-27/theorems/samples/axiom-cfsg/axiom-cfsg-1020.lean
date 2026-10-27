public section

namespace CFSG.RankThree.PartOne.U5E

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.S15K CFSG.RankThree.PartOne.U5K.Pkg CFSG.RankThree.PartOne.U5K
  CFSG.RankThree.PartOne.U5K.Kf

open CFSG.Assembly.RankThreeEven (projSU)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} {c : E}

variable (M : Model p E c)

omit [Finite G] in
theorem false_of_central {I S A : Subgroup G} (hSI : S ≤ I) (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S)
    (hSA : S = ⁅S, A⁆) (hcase : A ≤ I ∨ ¬ 2 ∣ Nat.card ↥(Subgroup.center ↥I))
    (hcent : ∀ (s : G) (hs : s ∈ S), (⟨s, hSI hs⟩ : ↥I) ∈ Subgroup.center ↥I) : False := by
  rcases hcase with hAI | hodd
  · apply hS1
    rw [hSA, eq_bot_iff]
    refine Subgroup.commutator_le.2 fun s hs a ha => ?_
    have h1 := Subgroup.mem_center_iff.1 (hcent s hs) ⟨a, hAI ha⟩
    have h2 : a * s = s * a := congrArg (fun z : ↥I => (z : G)) h1
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc s * a * s⁻¹ * a⁻¹ = (s * a) * s⁻¹ * a⁻¹ := rfl
      _ = (a * s) * s⁻¹ * a⁻¹ := by rw [← h2]
      _ = 1 := by group
  · obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS1
    obtain ⟨k, hk⟩ := hS2 s
    set z : ↥(Subgroup.center ↥I) := ⟨⟨(s : G), hSI s.2⟩, hcent s s.2⟩ with hz
    have hzk : z ^ 2 ^ k = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun w : ↥S => ((w : ↥S) : G)) hk
      simpa using this
    have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
    obtain ⟨j, hj, hjz⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hord : orderOf z = 1 := by
      by_contra hne
      have hj0 : j ≠ 0 := fun h0 => hne (by rw [hjz, h0]; rfl)
      have h2 : 2 ∣ orderOf z := by
        rw [hjz]
        exact dvd_pow_self 2 hj0
      exact hodd (h2.trans (orderOf_dvd_natCard z))
    have hz1 : z = 1 := orderOf_eq_one_iff.1 hord
    apply hs1
    apply Subtype.ext
    have := congrArg (fun w : ↥(Subgroup.center ↥I) => (((w : ↥I) : G))) hz1
    simpa [hz] using this

end CFSG.RankThree.PartOne.U5E
end
