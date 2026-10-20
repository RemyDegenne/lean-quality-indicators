public section

open Finset

namespace LinearMap

variable {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommMonoid M]
  [Module R M] [Module.Free R M]

theorem trace_restrictScalars_smul_of_pow_eq_one [Module.Free A R]
    [Module A M] [IsScalarTower A R M] (f : M →ₗ[R] M) (ε : R →ₐ[A] A) [IsLocalHom ε] {m : ℕ}
    (hm : IsUnit (m : A)) (hf : f ^ m = 1) (c : R) :
    trace A M ((c • f).restrictScalars A) = ε (trace R M f) * Algebra.trace A R c := by
  rw [trace_restrictScalars, map_smul, trace_eq_algebraMap_of_pow_eq_one f ε hm hf]
  simp [mul_comm c, ← Algebra.smul_def]

end LinearMap
end
