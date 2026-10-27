public section

open CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace RegularProperCurveCat

variable {k : Type u} [Field k]

/-- The transcendental function of `F` from which the model of `F` is built. -/
noncomputable def modelGenerator (F : FunctionFieldCat k) : F :=
  F.isFunctionField.exists_transcendental.choose

end RegularProperCurveCat
end TauCeti.AlgebraicGeometry
end
