@[expose] public section

universe u

noncomputable section

open CategoryTheory Functor Limits FintypeCat CompHausLike.LocallyConstant

namespace Condensed

section LocallyConstantAsColimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
  (c : Cone <| F ⋙ toProfinite) (X : Type (u + 1))

/-- The presheaf on `Profinite` of locally constant functions to `X`. -/
abbrev locallyConstantPresheaf : Profinite.{u}ᵒᵖ ⥤ Type (u + 1) :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u + 1}.obj X

end LocallyConstantAsColimit
end Condensed
end
end
