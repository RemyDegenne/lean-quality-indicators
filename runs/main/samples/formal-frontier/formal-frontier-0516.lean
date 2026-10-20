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

theorem fromTensorLimitDef_add
    (x y : DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
      (tensorMap A f M g N h · · ·)) :
    fromTensorLimitDef A f M g N h (x + y) =
      fromTensorLimitDef A f M g N h x + fromTensorLimitDef A f M g N h y := by
  induction x, y using DirectLimit.induction₂ with
  | _ i x y =>
    rw [DirectLimit.add_def, fromTensorLimitDef_mk, fromTensorLimitDef_mk,
      fromTensorLimitDef_mk, map_add]

end TensorProduct
end DirectLimit.VaryingScalar
end
