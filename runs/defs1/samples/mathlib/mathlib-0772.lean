@[expose] public section

open scoped Polynomial IntermediateField

open Module AlgEquiv IntermediateField

attribute [instance 100] IsGalois.to_isSeparable IsGalois.to_normal

section restrictRestrictAlgEquivMapHom

namespace IntermediateField

/--
The map from the `Gal(E/L)` to `Gal(K/F)` where `E/L/F` and `E/K/F` are two towers of
extensions induced by the restriction to `K`. Note that we do require `K/F` to be normal but not
`E/L`. If this is the case (and everything is finite dimensional) and `K ∩ L = F` then this
map is surjective, see `IntermediateField.restrictRestrictMapHom_surjective`.
This map is injective if the compositum of `K` and `L` is `E`,
see `IntermediateField.restrictRestrictAlgEquivMapHom_injective`.
-/
noncomputable def restrictRestrictAlgEquivMapHom (F K L E : Type*) [Field F] [Field K] [Field L]
    [Field E] [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
    [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K] :
    Gal(E/L) →* Gal(K/F) :=
  (AlgEquiv.restrictNormalHom K).comp (MulSemiringAction.toAlgAut Gal(E/L) F E)

end IntermediateField
end restrictRestrictAlgEquivMapHom
end
