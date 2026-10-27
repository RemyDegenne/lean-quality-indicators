public section

noncomputable section

open Polynomial TauCeti.ContCohomology

namespace TauCeti

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

namespace TwoDescent

local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])

local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))

local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])

variable [W.IsElliptic] [W.toAffine.IsCharNeTwoNF]

/-- Restriction to a factor field followed by the Weil-pairing character of its universal root. -/
noncomputable def factorCohomologicalMap (p : W.toAffine.f.Factors)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (𝕃 p))
    (h2 : IsUnit ((2 : ℕ) : K)) :
    H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2) →+
      H1 (AbsoluteGaloisGroup (𝕃 p)) (KummerCoeff (𝕃 p) 2) :=
  (explicitCoeff1 (AbsoluteGaloisGroup (𝕃 p))
      ((W.baseChange (𝕃 p)).TorsionCoeff 2) (factorTorsionCharacter W p h2)
      continuous_of_discreteTopology).comp (W.torsionRes τ 2)

end TwoDescent
end TauCeti
end
end
