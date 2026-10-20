@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace KTheory.K0

variable (R : Type uR) [CommRing R]

@[simp]
theorem of_mul
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type uN) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R M * of R N = of R (M ⊗[Rᵐᵒᵖ] N) := by
  calc
    of R M * of R N =
        ofClassRingHom R (ProjectiveClass.of R M * ProjectiveClass.of R N) :=
      ((ofClassRingHom R).map_mul _ _).symm
    _ = of R (M ⊗[Rᵐᵒᵖ] N) := by
      rw [ProjectiveClass.of_mul, ofClassRingHom_of]

end KTheory.K0
end
