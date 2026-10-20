@[expose] public section

universe u v w x

open DirectLimit

namespace DirectLimit.VaryingScalar

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

variable (A : ι → Type v) [∀ i, CommSemiring (A i)]

variable (f : ∀ i j, i ≤ j → A i →+* A j)

variable [DirectedSystem A (f · · ·)]

variable (M : ι → Type w) [∀ i, AddCommMonoid (M i)] [∀ i, Module (A i) (M i)]

variable (g : ∀ i j (h : i ≤ j), M i →ₛₗ[f i j h] M j)

variable [DirectedSystem M (g · · ·)]

section TensorProduct

variable (N : ι → Type x) [∀ i, AddCommMonoid (N i)] [∀ i, Module (A i) (N i)]

variable (h : ∀ i j (hij : i ≤ j), N i →ₛₗ[f i j hij] N j)

variable [DirectedSystem N (h · · ·)]

@[simp]
theorem fromTensorLimit_mk (i : ι) (x : TensorProduct (A i) (M i) (N i)) :
    fromTensorLimit A f M g N h ⟦⟨i, x⟩⟧ = tensorToLimits A f M g N h i x :=
  rfl

end TensorProduct
end DirectLimit.VaryingScalar
end
