@[expose] public section

universe t u

noncomputable section

open TensorProduct

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

section Module

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
  (f g : N →ₗ[R] P)

/-- The bilinear map corresponding to `LinearMap.tensorEqLocus`. -/
def LinearMap.tensorEqLocusBil :
    M →ₗ[S] LinearMap.eqLocus f g →ₗ[R]
      LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
        (AlgebraTensorModule.lTensor S M g) where
  toFun m :=
    { toFun := fun a ↦ ⟨m ⊗ₜ a, by simp [show f a = g a from a.property]⟩
      map_add' := fun x y ↦ by simp [tmul_add]
      map_smul' := fun r x ↦ by simp }
  map_add' x y := by
    ext
    simp [add_tmul]
  map_smul' r x := by
    ext
    simp [smul_tmul']

end Module
end
end
