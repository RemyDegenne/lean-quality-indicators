public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

noncomputable section

namespace SpectralStoneDuality

variable {J : Type v} [Category.{w} J] [IsCofiltered J]

variable (D : J ⥤ TopCat.{max v u}) (C : Cone D)

/-- The inverse image of a compact open under a specified cone projection. -/
@[expose]
def compactOpenCylinder (k : compactOpenCylinderIndex D) : Opens C.pt :=
  (Opens.map (C.π.app k.1)).obj k.2.1

end SpectralStoneDuality
end
end
