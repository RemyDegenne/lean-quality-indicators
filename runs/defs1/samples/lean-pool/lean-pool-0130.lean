universe u

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.DegreeTwoExample

open Set

/-- The coefficient-doubled comparison element. It has the same support as `degreeTwoOz`, but its
factorisation as `2 * degreeTwoOz` is visible in the definition. -/
def degreeTwoFoil : Oz.OmnificInteger.{u} :=
  2 * degreeTwoOz

end ConwayRefinement.Standalone.Oz.DegreeTwoExample
end
