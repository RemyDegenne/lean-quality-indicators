public section

noncomputable section

open IsDedekindDomain NumberField Module Polynomial

open scoped TensorProduct NumberField AdicCompletionExtension Valued

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

/-- The normalized irreducible factors over `K_v` of the chosen primitive element's minimal
polynomial. -/
abbrev completionFactors :=
  {q : (v.adicCompletion K)[X] //
    Irreducible q ∧ q.Monic ∧ q ∣ completionPolynomial L v}

end TauCeti
end
end
