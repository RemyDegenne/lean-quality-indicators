@[expose] public section

universe u v w x y z u' v' w' x' y'

variable {R : Type u} {M : Type v} {M₂ : Type w}

variable {M₃ : Type y} {ι : Type x} {ι' : Type x'}

open Function Submodule

namespace LinearMap

universe i

variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι → Type i} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps]
protected def compLeft (f : M₂ →ₗ[R] M₃) (I : Type*) : (I → M₂) →ₗ[R] I → M₃ :=
  { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }

end LinearMap
end
