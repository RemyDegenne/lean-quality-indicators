public section

open CategoryTheory

open TauCeti.DynkinType

namespace TauCeti.E7Minuscule

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

@[simp↓]
theorem mem_weightTorusDefiningIdeal (x : coordinateHopfAlgebra R) :
    x ∈ weightTorusDefiningIdeal R ↔ (weightTorusToBaseChangeCoordinateMap R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

end
end TauCeti.E7Minuscule
end
