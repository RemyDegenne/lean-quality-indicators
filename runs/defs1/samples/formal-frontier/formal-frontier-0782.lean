set_option warningAsError true

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PullbackOpenImmersion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The second projection, restricted to the complement of `ker g`. -/
def sndOpenMap (f : R →+* T) (g : S →+* T) :
    (sndSource f g : Scheme) ⟶ Spec (.of (f.pullback g)) :=
  (sndSource f g).ι ≫ sndMap f g

end AlgebraicGeometry.PullbackOpenImmersion
end
end
