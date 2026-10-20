@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

/-- Turn a non-unital subring containing `1` into a subring. -/
def NonUnitalSubring.toSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) : Subring R where
  __ := S
  one_mem' := h1

end
