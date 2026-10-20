public section

namespace AlgHom

section Semiring

variable {F A C B : Type*} [CommSemiring F] [Semiring A] [Algebra F A] [Semiring C] [Algebra F C]
  [Semiring B] [Algebra F B]

theorem prodFirst_surjective (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1)
    (hφ : Function.Surjective φ) : Function.Surjective (prodFirst φ hu) := by
  rw [← prodFirst_comp_fst φ hu, AlgHom.coe_comp] at hφ
  exact hφ.of_comp

end Semiring
end AlgHom
end
