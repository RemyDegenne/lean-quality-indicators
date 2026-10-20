namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleLocalModel

section Loc

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

scoped instance awayMap_isLocalizedModule (r : B) (M : FullLattice 𝒪 K) :
    IsLocalizedModule (Submonoid.powers r) (awayMap (𝒪 := 𝒪) (K := K) r M) := by
  infer_instance

scoped instance locMap_isLocalizedModule (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) :
    IsLocalizedModule x.asIdeal.primeCompl (locMap (𝒪 := 𝒪) (K := K) x M) := by
  infer_instance

theorem lineBaseChange_toLocRing_eq_localized' (x : PrimeSpectrum B) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    lineBaseChange (toLocRing B x) M N = N.localized' (locRing B x) x.asIdeal.primeCompl (locMap x M) := by
  have hfun : (⇑(LinearMap.rTensor (↥M.1) (toLocRing B x).toLinearMap) :
      latticeBaseChange 𝒪 K B M → latticeBaseChange 𝒪 K (locRing B x) M) = ⇑(locMap x M) :=
    funext fun z => (locMap_apply x M z).symm
  rw [Submodule.localized'_eq_span, lineBaseChange, hfun]

end Loc
end P2mKcQuadrupleLocalModel
end
end P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map
