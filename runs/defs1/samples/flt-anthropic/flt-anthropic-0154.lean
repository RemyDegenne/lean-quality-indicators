set_option autoImplicit false

noncomputable section

open Deep.NTSupply NumberField IsDedekindDomain WithZero

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell.P2.Artin

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter WithZero

section Admissible

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

def IsAdmissibleModulus (𝔣 : Ideal (𝓞 K)) : Prop :=
  𝔣 ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K), (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ → v.asIdeal ^ admissibleExp K v ∣ 𝔣

end Admissible
end LanglandsTunnell.P2.Artin
end
