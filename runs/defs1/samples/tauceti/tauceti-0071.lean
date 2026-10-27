public section

namespace NumberField.Chebotarev

open Filter TauCeti

open scoped Asymptotics nonZeroDivisors NumberField

open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

variable (K L) in
/-- The logarithmic weight on prime powers selected by their powered Artin class. -/
noncomputable def frobeniusPrimePowerWeight (C : ConjClasses (L ≃ₐ[K] L))
    (A : IdealPrimePower K) : ℝ :=
  (frobeniusPrimePowerSet K L C).indicator primePowerWeight A

end NumberField.Chebotarev
end
