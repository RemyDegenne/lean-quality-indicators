@[expose] public section

noncomputable section

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]

variable (M : Type v) [AddCommGroup M] [Module R M]

theorem determinant_comp (n : ℕ) [Module.Invertible R (⋀[R]^n M)]
    (f g : Module.End R M) :
    determinant R M n (f.comp g) =
      determinant R M n f * determinant R M n g := by
  simpa only [Module.End.mul_eq_comp] using (determinant R M n).map_mul f g

end exteriorPower
end
end
