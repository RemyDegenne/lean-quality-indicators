public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

noncomputable section

namespace SpectralStoneDuality

variable {J : Type v} [Category.{w} J] [IsCofiltered J]

variable (D : J ⥤ TopCat.{max v u}) (C : Cone D)

variable {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- An index for compact-open cylinders of an inverse system over `Iᵒᵖ`. -/
@[expose]
def directedCompactOpenCylinderIndex (E : Iᵒᵖ ⥤ TopCat.{v}) :=
  Σ i : I, {U : Opens (E.obj (op i)) // IsCompact (U : Set (E.obj (op i)))}

end SpectralStoneDuality
end
end
