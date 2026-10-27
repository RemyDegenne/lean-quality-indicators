public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_primeCore_of_quotient {M : Subgroup G}
    (hD : Group.IsSolvable ↥(rankThreePrimeCore 3 M))
    (hQ : Group.IsSolvable (↥M ⧸ primeComplementCore (G := ↥M) 3)) : Group.IsSolvable ↥M := by
  have hN : Group.IsSolvable ↥(primeComplementCore (G := ↥M) 3) := by
    rw [stepC_primeCore_eq_map] at hD
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((primeComplementCore (G := ↥M) 3).equivMapOfInjective M.subtype
        M.subtype_injective).toMonoidHom) (MulEquiv.injective _)
  exact Group.isSolvable_of_subgroup_quotient (primeComplementCore (G := ↥M) 3)

end CFSG.LocalAnalysis.RankThreeTheoremC
end
