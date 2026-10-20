namespace P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_forall_isUnit_tensorProduct_padic_iff

set_option autoImplicit false

open scoped Quaternion TensorProduct

open IsDedekindDomain NumberField

namespace RamifiedPadicDictionary

theorem natGenerator_placeOf (ℓ : ℕ) [Fact ℓ.Prime] :
    Rat.HeightOneSpectrum.natGenerator (placeOf ℓ) = ℓ :=
  congrArg Subtype.val (primesEquiv_placeOf ℓ)

end RamifiedPadicDictionary
end P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_forall_isUnit_tensorProduct_padic_iff
