@[expose] public section

variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

variable {M}

namespace Con

section MulOneClass

variable [MulOneClass M] [MulOneClass N] [MulOneClass P] {c : Con M}

variable (c)

variable (x y : M)

variable {c}

@[to_additive ]
theorem comap_eq {f : N →* M} : comap f f.map_mul c = ker (c.mk'.comp f) :=
  ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq]; rfl

end MulOneClass
end Con
end
