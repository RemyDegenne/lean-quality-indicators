@[expose] public section

universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

namespace NonUnitalSubring

@[simp]
theorem coe_copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

end NonUnitalSubring
end Basic
end
