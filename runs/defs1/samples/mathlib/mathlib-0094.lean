@[expose] public section

universe u v w x y z u' v' w' x' y'

variable {R : Type u} {M : Type v} {M₂ : Type w}

variable {M₃ : Type y} {ι : Type x} {ι' : Type x'}

open Function Submodule

namespace LinearMap

universe i

variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι → Type i} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

/-- Construct a linear map between two (dependent) function spaces
by applying index-dependent linear maps to the coordinates.
A bundled version of `Pi.map`.

If the index type is finite, then this map can be seen as a “block diagonal” map
between indexed products of modules. -/
def piMap {ψ : ι → Type*} [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)]
    (f : ∀ i, φ i →ₗ[R] ψ i) : (∀ i, φ i) →ₗ[R] (∀ i, ψ i) :=
  .pi fun i ↦ f i ∘ₗ proj i

end LinearMap
end
