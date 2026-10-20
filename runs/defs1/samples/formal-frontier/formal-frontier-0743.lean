set_option warningAsError true

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PullbackOpenImmersion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The restricted source of the second projection. -/
def sndSource (_f : R →+* T) (g : S →+* T) : (Spec (.of S)).Opens :=
  kernelComplement g

end AlgebraicGeometry.PullbackOpenImmersion
end
end
