public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

variable [(Q.subgroupOf M).Normal]

theorem Ctx.exists_normal_normalizer_LB_of_isA2 (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) :
    ∃ K : Subgroup (Mbar M Q),
      K ≤ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)) ∧
      (∀ c ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)),
          ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      (∀ x ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)),
          (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 ∈ K) ∧
      K ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  obtain ⟨k, γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp hD
  exact hc.exists_normal_normalizer_LB_of_model hD hφπ hφker hφiso ha hA

end CFSG.RankThree.GF2n.Stroth80
end
