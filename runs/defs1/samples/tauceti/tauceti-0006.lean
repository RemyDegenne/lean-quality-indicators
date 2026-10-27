public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius) {X Y : C}

/-- The cone sequence `Y ⟶ cone(f) ⟶ ΣX`. It is the cobase change of the chosen suspension
presentation of `X` along `-f`. -/
noncomputable abbrev coneSequence (f : X ⟶ Y) : ShortComplex C :=
  ShortComplex.mk (hE.coneInclusion f) (hE.coneConnectingMap f)
    (hE.coneInclusion_comp_coneConnectingMap f)

end ExactStructure.IsFrobenius
end TauCeti
end
