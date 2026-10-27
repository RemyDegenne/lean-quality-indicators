public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix

open CFSG.Assembly.LowTwoRank

open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauEquiv tauAut tauAut_proj tauMat_apply
  tauPair_ι₀ tauPair_ι₁ tauPair_ι₂ tauPair_ι₃)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Torus

variable {p : ℕ}

omit [Finite K] in
theorem fieldRev_torC (σ : K ≃+* K) (v : D8Mod p K) :
    fieldRev σ (torC p K v) = torC p K (sigVec σ v) := by
  rw [torC_apply, fieldRev_tpt]
  rfl

end Torus
end CFSG.RankThree.PartOne.SP4C
end
