@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

namespace Subring

/-- Turn a `Subring` into a `NonUnitalSubring` by forgetting that it contains `1`. -/
@[reducible]
def toNonUnitalSubring (S : Subring R) : NonUnitalSubring R where __ := S

end Subring
end
