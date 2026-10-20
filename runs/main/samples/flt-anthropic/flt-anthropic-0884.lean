namespace P2MW.S_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing

set_option autoImplicit false

universe u

noncomputable section

open Polynomial WeierstrassCurve

namespace ModularCurve

namespace LevelP

namespace FlatProof

p2m_open

variable {B : Type u} [CommRing B]

theorem flat_vcRing (p : ℕ) : Module.Flat (UnivBasisRing p) (VCRing p) := by
  haveI : Module.Flat (VCPoly p) (VCRing p) :=
    IsLocalization.flat (VCRing p) (Submonoid.powers (MvPolynomial.X 0 : VCPoly p))
  exact Module.Flat.trans (UnivBasisRing p) (VCPoly p) (VCRing p)

end FlatProof
end LevelP
end ModularCurve
end
end P2MW.S_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing
