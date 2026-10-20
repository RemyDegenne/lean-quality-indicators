public section

open Matrix

namespace TauCeti.GLSymplecticFin

universe u v

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

@[simp]
theorem map_positiveLongRootWeylElement {S : Type v} [CommRing S]
    (f : R →+* S) (i : Fin m) :
    GLSymplecticFin.map m R f (positiveLongRootWeylElement i) =
      positiveLongRootWeylElement i := by
  simp [positiveLongRootWeylElement]

end TauCeti.GLSymplecticFin
end
