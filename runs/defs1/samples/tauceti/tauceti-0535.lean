public section

noncomputable section

namespace TauCeti

variable (F E : Type*) [Field F] [Field E] [Algebra F E] (M : IntermediateField F E) [Normal F M]

variable [Normal F E]

/-- **The Galois group of a normal subextension is a quotient of the Galois group**, as a
topological group: for `E/F` and `M/F` normal, restriction induces an isomorphism
`Gal(E/F) ⧸ M.fixingSubgroup ≃ₜ* Gal(M/F)`. -/
def quotientFixingSubgroupEquiv : Gal(E/F) ⧸ M.fixingSubgroup ≃ₜ* Gal(↥M/F) where
  __ := quotientFixingSubgroupMulEquiv F E M
  __ := Continuous.homeoOfEquivCompactToT2 (f := (quotientFixingSubgroupMulEquiv F E M).toEquiv)
    (continuous_quotientFixingSubgroupMulEquiv F E M)

end TauCeti
end
end
