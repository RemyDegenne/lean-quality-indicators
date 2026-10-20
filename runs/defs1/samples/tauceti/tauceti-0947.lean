public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe v

variable (R : Type v) [CommRing R]

/-- The Koszul braiding of two cochain complexes of `R`-modules, as an isomorphism.  It is its own
inverse up to swapping the factors, since `ModuleCat R` is symmetric and the Koszul sign is. -/
noncomputable def koszulBraiding (X Y : CochainComplex (ModuleCat.{v} R) ℤ) : X ⊗ Y ≅ Y ⊗ X where
  hom := koszulBraidingHom R X Y
  inv := koszulBraidingHom R Y X
  hom_inv_id := koszulBraidingHom_comp R X Y
  inv_hom_id := koszulBraidingHom_comp R Y X

end TauCeti
end
