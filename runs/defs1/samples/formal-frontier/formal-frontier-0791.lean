public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

noncomputable section

namespace SpectralStoneDuality

variable {J : Type v} [Category.{w} J] [IsCofiltered J]

variable (D : J ⥤ TopCat.{max v u}) (C : Cone D)

/-- A compact-open stage cylinder on the actual chosen limit of a diagram. -/
@[expose]
def chosenLimitCompactOpenCylinder [HasLimit D]
    (k : compactOpenCylinderIndex D) : Opens ((limit D : TopCat.{max v u})) :=
  (Opens.map (limit.π D k.1)).obj k.2.1

end SpectralStoneDuality
end
end
