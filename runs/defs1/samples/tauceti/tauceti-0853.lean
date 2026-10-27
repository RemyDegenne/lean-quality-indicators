public noncomputable section

universe u

open CategoryTheory Limits Rep groupCohomology

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G]

variable (R G) in
/-- The complex of inhomogeneous cochains extended by zero to negative degrees, as a functor. -/
-- The object must remain exposed: public comparisons use the connected complex as their
-- source, and consumers construct maps with the same cochain carriers.
@[expose]
def cochainsExtFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := (cochainsConnectData M).cochainComplex
  map f := CochainComplex.ConnectData.map _ _ (𝟙 _) (cochainsMap (.id G) f) (by simp)
  map_id M := by
    simpa only [cochainsMap_id] using CochainComplex.ConnectData.map_id (cochainsConnectData M)
  map_comp f g := by
    simp only [cochainsMap_id_comp, CochainComplex.ConnectData.map_comp_map, Category.comp_id]

end TauCeti.TateCohomology
end
