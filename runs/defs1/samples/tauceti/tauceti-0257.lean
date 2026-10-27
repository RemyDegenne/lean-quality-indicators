public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

local notation "F" => ZMod 2

local notation "C" => GridChain F n

local notation "N" => StabilizeXOffCenterState G s →₀ F

local notation "G'" => stabilizeX G (Fin.castSucc s) (Fin.castSucc (G.X s)) s

local notation "D" => fullyBlockedDifferential G'

local notation "DI" => G.fullyBlockedDifferential

local notation "P" => LinearMap.constantCoeffReduction (stabilizeXCenterProjection G s F)

local notation "Q" => LinearMap.constantCoeffReduction (stabilizeXOffCenterProjection G s F)

local notation "I" => LinearMap.constantCoeffReduction (stabilizeXCenterInclusion G s F)

local notation "J" => LinearMap.constantCoeffReduction (stabilizeXOffCenterInclusion G s F)

local notation "K" => LinearMap.constantCoeffReduction (stabilizeXConnecting G s F)

local notation "H" => LinearMap.constantCoeffReduction (stabilizeXOffCenterToCenter G s F)

local notation "E" => LinearMap.constantCoeffReduction (stabilizeXOffCenterDifferential G s F)

/-- The fully blocked homology of an `X`-split stabilization is two copies of the original
homology. The equivalence is induced by `fullyBlockedStabilizeXMap`; it concerns ungraded
vector spaces. -/
noncomputable def fullyBlockedHomologyStabilizeXEquivProd :
    (G').fullyBlockedHomology ≃ₗ[F] G.fullyBlockedHomology × G.fullyBlockedHomology :=
  (G').fullyBlockedHomologyEquivLinearMapHomology.trans
    ((LinearEquiv.ofBijective
      (LinearMap.homologyMap (G.fullyBlockedStabilizeXMap s)
        (G').fullyBlockedDifferential_comp_self_eq_zero G.prod_d_squared
        (G.fullyBlockedStabilizeXMap_comp_differential s))
      (G.fullyBlockedStabilizeXMap_homologyMap_bijective s)).trans
      (((DI).homologyProdEquiv DI G.fullyBlockedDifferential_comp_self_eq_zero
        G.fullyBlockedDifferential_comp_self_eq_zero).trans
        (G.fullyBlockedHomologyEquivLinearMapHomology.symm.prodCongr
          G.fullyBlockedHomologyEquivLinearMapHomology.symm)))

end TauCeti.GridDiagram
end
