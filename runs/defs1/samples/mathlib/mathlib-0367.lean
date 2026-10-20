@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-- The range of a ring homomorphism, as a subring of the target. See Note [range copy pattern]. -/
def range (f : R →+* S) : Subring S :=
  ((⊤ : Subring R).map f).copy (Set.range f) Set.image_univ.symm

end RingHom
end
