@[expose] public section

universe u v

namespace IsCoprime

section CommRing

variable {R : Type u} [CommRing R]

@[simp] theorem add_mul_left_right_iff {x y z : R} : IsCoprime x (y + x * z) ↔ IsCoprime x y :=
  ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩

end CommRing
end IsCoprime
end
