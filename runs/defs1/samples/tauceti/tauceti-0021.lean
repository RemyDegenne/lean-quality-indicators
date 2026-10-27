public section

noncomputable section

open IsDedekindDomain NumberField Module Polynomial

open scoped TensorProduct NumberField AdicCompletionExtension Valued

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

/-- A chosen primitive power basis for a finite extension of number fields. -/
def semilocalPowerBasis : PowerBasis K L :=
  Field.powerBasisOfFiniteOfSeparable K L

end TauCeti
end
end
