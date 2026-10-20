@[expose] public section

universe u v w x

namespace MvPolynomial

variable {R : Type u} {S : Type v} {σ : Type w}

variable [CommSemiring R] [CommSemiring S]

@[simp]
theorem comap_map_C (I : Ideal R) :
    (Ideal.map (C : R →+* MvPolynomial σ R) I).comap C = I := by
  ext r
  rw [Ideal.mem_comap, ← C_mem_coeffsIn (σ := σ) (M := (I : Submodule R R)),
    coeffsIn_eq_restrictScalars_map_C, Submodule.restrictScalars_mem]

end MvPolynomial
end
