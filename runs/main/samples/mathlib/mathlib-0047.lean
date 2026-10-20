@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

namespace Subring

variable (s : Subring R)

@[norm_cast]
theorem coe_natCast (n : ℕ) : ((n : s) : R) = n := rfl

end Subring
end
