@[expose] public section

universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BddDistLat extends DistLat where
  [isBoundedOrder : BoundedOrder toDistLat]

end
