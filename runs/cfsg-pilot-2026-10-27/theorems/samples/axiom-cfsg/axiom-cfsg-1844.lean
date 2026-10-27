public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.ComponentClassification.OuterAutomorphisms

open scoped commutatorElement

theorem not_dvd_card_of_perfect_central_sylow {J : Type*} [Group J] [Finite J] {p : ℕ}
    [Fact p.Prime] (hperf : Group.IsPerfect J) (P : Sylow p J)
    (hP : (P : Subgroup J) ≤ Subgroup.center J) : ¬ p ∣ Nat.card J := by
  intro hdvd
  have hN : Subgroup.normalizer (P : Subgroup J) ≤ Subgroup.centralizer (P : Set J) := by
    intro n _ c hc
    exact (Subgroup.mem_center_iff.1 (hP hc) n).symm
  let φ := MonoidHom.transferSylow P hN
  have hcomm : ∀ x y : ↥P, ⁅x, y⁆ = 1 := by
    intro x y
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hP x.2) y).symm
  have hker : (⊤ : Subgroup J) ≤ φ.ker := by
    rw [← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hcomm _ _
  have hPbot : (P : Subgroup J) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : φ g = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top g))
    rw [MonoidHom.transferSylow_eq_pow P hN g hg] at h1
    have h2 : g ^ (P : Subgroup J).index = 1 := congrArg Subtype.val h1
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
    have hgk : g ^ p ^ k = 1 := congrArg Subtype.val hk
    have h3 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hgk
    have h4 : orderOf g ∣ (P : Subgroup J).index := orderOf_dvd_of_pow_eq_one h2
    have h5 := Nat.eq_one_of_dvd_coprimes
      ((Nat.Coprime.pow_left k ((Fact.out : p.Prime).coprime_iff_not_dvd.2 P.not_dvd_index))) h3 h4
    rw [orderOf_eq_one_iff.1 h5]
    exact Subgroup.one_mem _
  have := P.dvd_card_of_dvd_card hdvd
  rw [hPbot, Subgroup.card_bot] at this
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 this)

end CFSG.HardMathSupport.Solomon.Coordinator
end
