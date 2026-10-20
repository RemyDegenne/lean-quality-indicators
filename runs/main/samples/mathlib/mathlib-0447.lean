@[expose] public section

open scoped Polynomial IntermediateField

open Module AlgEquiv IntermediateField

attribute [instance 100] IsGalois.to_isSeparable IsGalois.to_normal

section GaloisCorrespondence

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

variable (H : Subgroup Gal(E/F)) (K : IntermediateField F E)

namespace IntermediateField

@[simp]
theorem coe_subgroupEquivAlgEquiv_symm_apply [FiniteDimensional F E] (σ : Gal(E/fixedField H)) :
    ⇑((subgroupEquivAlgEquiv H).symm σ).1 = ⇑σ :=
  rfl

end IntermediateField
end GaloisCorrespondence
end
