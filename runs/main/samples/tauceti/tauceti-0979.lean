public noncomputable section

universe u

open CategoryTheory Representation

namespace TauCeti.TateCohomology

variable {R G H K : Type u} [CommRing R] [Group G] [Group H] [Group K]
  {M : Rep R G} {N : Rep R H} {P : Rep R K}

section Degrees

variable [Fintype G] [Fintype H] [Fintype K]

@[simp] theorem complexMap_id :
    complexMap (e := MulEquiv.refl G) (φ := LinearMap.id) (Rep.isIntertwiningMap_id M) =
      𝟙 (tateComplex M) := by
  rw [complexMap_refl]
  exact (tateComplexFunctor R G).map_id M

end Degrees
end TauCeti.TateCohomology
end
