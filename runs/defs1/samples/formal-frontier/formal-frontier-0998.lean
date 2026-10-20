set_option warningAsError true

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PullbackOpenImmersion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The common map from a fiber product of rings to its base. -/
def toBase (f : R →+* T) (g : S →+* T) : f.pullback g →+* T :=
  f.comp (f.pullbackFst g)

end AlgebraicGeometry.PullbackOpenImmersion
end
end
