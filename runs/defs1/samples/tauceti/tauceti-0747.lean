public noncomputable section

universe u

open CategoryTheory LinearMap Rep Representation

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] (M : Rep R G)
  (H : Subgroup G)

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

section Zero

/-- Corestriction from a subgroup in degree zero Tate cohomology, induced by the relative norm
`Mᴴ → Mᴳ`. -/
def H0Cor : tateCohomology (Rep.res H.subtype M) 0 ⟶ tateCohomology M 0 :=
  (H0IsoNormQuotient (Rep.res H.subtype M)).hom ≫
    ModuleCat.ofHom (Submodule.mapQ _ _ _ (h0_cor_le M H)) ≫
    (H0IsoNormQuotient M).inv

end Zero
end TauCeti.TateCohomology
end
