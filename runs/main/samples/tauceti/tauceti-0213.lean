public section

open IntermediateField MulAction

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace IntermediateField

section Galois

variable [IsGalois K L]

@[simp]
theorem quotientNormalizerEquivConjugateFields_mk (E : IntermediateField K L)
    (σ : L ≃ₐ[K] L) :
    ((quotientNormalizerEquivConjugateFields E) (QuotientGroup.mk σ)).1 = σ • E := by
  simp only [quotientNormalizerEquivConjugateFields, Equiv.trans_apply,
    Subgroup.quotientEquivOfEq_mk, Equiv.subtypeEquivRight_apply,
    MulAction.orbitEquivQuotientStabilizer_symm_apply]

end Galois
end IntermediateField
end
