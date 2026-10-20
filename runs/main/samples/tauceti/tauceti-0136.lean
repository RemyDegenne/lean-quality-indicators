public noncomputable section

universe u

open CategoryTheory Representation

namespace TauCeti.TateCohomology

variable {R G H K : Type u} [CommRing R] [Group G] [Group H] [Group K]
  {M : Rep R G} {N : Rep R H} {P : Rep R K}

section Degrees

variable [Fintype G] [Fintype H] [Fintype K]

@[simp] theorem complexMapIso_hom {e : G ≃* H} {e' : M.V ≃ₗ[R] N.V}
    (he : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* H)) (e' : M.V →ₗ[R] N.V)) :
    (complexMapIso he).hom = complexMap he := by
  rw [complexMapIso]

end Degrees
end TauCeti.TateCohomology
end
