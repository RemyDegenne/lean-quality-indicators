public section

universe u v w

open CategoryTheory TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

section ChartAlgebra

variable (R)

namespace ChartAlgebra

variable (x : Fin k → M)

/-- The universal point of the chart at `x`: the linear map `M → (ChartAlgebra R x)^k` whose `j`-th
component sends `m` to the class of the generator `Pi.single j m` of the symmetric algebra. -/
noncomputable def universalLinearMap : M →ₗ[R] Fin k → ChartAlgebra R x :=
  LinearMap.pi fun j ↦ (Ideal.Quotient.mkₐ R (chartIdeal R x)).toLinearMap ∘ₗ
    SymmetricAlgebra.ι R (Fin k → M) ∘ₗ LinearMap.single R (fun _ ↦ M) j

end ChartAlgebra
end ChartAlgebra
end Module.Grassmannian
end
