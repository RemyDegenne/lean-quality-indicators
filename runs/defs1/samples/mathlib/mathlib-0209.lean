@[expose] public section

open Module

variable (G G' K L : Type*) [Group G] [Group G'] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [MulSemiringAction G' L]

namespace IsGaloisGroup

attribute [instance low] commutes isInvariant

variable (H H' : Subgroup G) (F F' : IntermediateField K L)

section GaloisCorrespondence

section IsGaloisGroup

variable [hGKL : IsGaloisGroup G K L]

/-- The Galois correspondence from intermediate fields to subgroups. -/
noncomputable def intermediateFieldEquivSubgroup [Finite G] :
    IntermediateField K L ≃o (Subgroup G)ᵒᵈ :=
  have := isGalois G K L
  have := finiteDimensional G K L
  IsGalois.intermediateFieldEquivSubgroup.trans (mulEquivAlgEquiv G K L).comapSubgroup.dual

end IsGaloisGroup
end GaloisCorrespondence
end IsGaloisGroup
end
