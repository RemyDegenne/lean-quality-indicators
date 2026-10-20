set_option warningAsError true

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PullbackOpenImmersion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The restricted source of the first projection. -/
def fstSource (f : R →+* T) (_g : S →+* T) : (Spec (.of R)).Opens :=
  kernelComplement f

end AlgebraicGeometry.PullbackOpenImmersion
end
end
