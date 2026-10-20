public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped AdeleGaloisAction Pointwise TensorProduct

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

scoped[AdeleGaloisAction] attribute [instance]
  TauCeti.GlobalNumberFields.ideleMulDistribMulAction

variable {K L}

scoped[AdeleGaloisAction] attribute [instance]
  TauCeti.GlobalNumberFields.ideleClassMulDistribMulAction

variable (S : Set (HeightOneSpectrum (𝓞 K)))

variable {S}

@[simp]
theorem mem_sIdeles_iff {x : IdeleGroup (𝓞 L) L} :
    x ∈ sIdeles L S ↔ ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
      Valued.v (w.ideleFiniteCoord x : w.adicCompletion L) = 1 := by
  simp [sIdeles]

end TauCeti.GlobalNumberFields
end
end
