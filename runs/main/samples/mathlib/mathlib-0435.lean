@[expose] public section

noncomputable section

open Algebra (FinitePresentation FiniteType)

open Ideal Module Polynomial

variable {R S T U K : Type*}

namespace AdjoinRoot

section CommRing

variable [CommRing R] (f g : R[X])

variable {f g}

variable [CommRing S]

variable {i : R →+* S} {a : S} (h : f.eval₂ i a = 0)

variable [CommRing T]

@[simp] lemma coe_mapRingEquiv (f : R ≃+* S) (p : R[X]) (q : S[X]) (h) :
    ⇑(mapRingEquiv f p q h) = map f p q h.symm.dvd := rfl

end CommRing
end AdjoinRoot
end
end
