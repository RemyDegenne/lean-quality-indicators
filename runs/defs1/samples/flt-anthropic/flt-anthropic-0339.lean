namespace P2MW.S_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain

namespace P2mS26Univ

noncomputable section

open IsDedekindDomain NumberField

open scoped NumberField.PlaceTransport

universe uK uL

attribute [local instance] small

attribute [local instance] numberField alg isGalois

section products

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (L) (S : Finset (HeightOneSpectrum (𝓞 K)))

variable {S}

def PhiF0 (Φf : (v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) → MulAut (Π w : Fib K L v.1, w.1.adicCompletion L)ˣ)
    (v0 : {v0 : HeightOneSpectrum (𝓞 (Shrink.{0} K)) // v0 ∈ S0 S}) :
    MulAut (Π w0 : Fib0 K L v0.1, w0.1.adicCompletion (Shrink.{0} L))ˣ :=
  MulAut.congr (ΨF (hv0 v0.1)) (Φf (splcInv v0))

end products
end
end P2mS26Univ
end P2MW.S_M4aHerbrand_finSIdeleFibreBox_tateCard_eq_localDegreeProd
