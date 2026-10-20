public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- The **maximal abelian extension** `K^{ab}` of `K` in `Ω`: the compositum of all intermediate
fields of `Ω/K` that are abelian Galois over `K`. -/
def maximalAbelianExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsAbelianGalois K E}, (E : IntermediateField K Ω)

end TauCeti
end
end
