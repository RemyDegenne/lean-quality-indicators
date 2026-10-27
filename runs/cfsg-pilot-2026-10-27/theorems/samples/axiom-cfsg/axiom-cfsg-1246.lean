public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

section Abstract

variable {X : Type*} [Group X]

theorem szd_card_sup_zpowers {A : Subgroup X} (hA : IsMulCommutative A) {g : X} (hg : g ∉ A)
    (hg5 : g ^ 5 = 1) (hcomm : ∀ a ∈ A, a * g = g * a) :
    Nat.card (A ⊔ Subgroup.zpowers g : Subgroup X) = Nat.card A * 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : ∀ (a : A) (n : Subgroup.zpowers g),
      Commute (A.subtype a) ((Subgroup.zpowers g).subtype n) := by
    rintro ⟨a, ha⟩ ⟨n, hn⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact Commute.zpow_right (hcomm a ha) k
  set f := MonoidHom.noncommCoprod A.subtype (Subgroup.zpowers g).subtype hc with hf_def
  have hrange : f.range = A ⊔ Subgroup.zpowers g := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hg1 : g ≠ 1 := fun h => hg (h ▸ A.one_mem)
  have hord : orderOf g = 5 := orderOf_eq_prime hg5 hg1
  have hfin : Finite (Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; norm_num)
  have hdisj : Disjoint A (Subgroup.zpowers g) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro u ⟨huA, hug⟩
    rw [Subgroup.mem_bot]
    by_contra hu1
    apply hg
    have hle : Subgroup.zpowers u ≤ Subgroup.zpowers g := Subgroup.zpowers_le.mpr hug
    have hordu : orderOf u = 5 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp
        (hord ▸ orderOf_dvd_of_mem_zpowers hug) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hu1
      · exact h
    have heq : Subgroup.zpowers u = Subgroup.zpowers g :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordu])
    exact (Subgroup.zpowers_le.mpr huA) (heq ▸ Subgroup.mem_zpowers g)
  have hinj : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr ⟨A.subtype_injective, Subtype.val_injective,
      by rwa [Subgroup.range_subtype, Subgroup.range_subtype]⟩
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod,
    Nat.card_zpowers, hord]

end Abstract
end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
end
