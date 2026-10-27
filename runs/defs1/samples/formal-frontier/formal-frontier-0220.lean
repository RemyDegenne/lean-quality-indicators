set_option warningAsError true

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PullbackOpenImmersion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The image of the second restricted map is the complement of the *first*
projection kernel. -/
def sndTarget (f : R →+* T) (g : S →+* T) :
    (Spec (.of (f.pullback g))).Opens :=
  kernelComplement (f.pullbackFst g)

end AlgebraicGeometry.PullbackOpenImmersion
end
end
