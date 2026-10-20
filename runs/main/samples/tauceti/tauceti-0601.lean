public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

variable {O} in
theorem IsSharpSemiGlobalMinimalAt.obstructionExponentAt_eq_one {v₀ : HeightOneSpectrum O}
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : IsSharpSemiGlobalMinimalAt O v₀ W) :
    obstructionExponentAt O v₀ W = 1 :=
  hW.2.2

end WeierstrassCurve
end
