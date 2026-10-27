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

/-- The canonical semilinear map from a stage module to its varying-scalar limit. -/
def of (i : ι) : M i →ₛₗ[DirectLimit.Ring.of A (f · · ·) i]
    DirectLimit M (fun i j h ↦ g i j h) where
  toFun m := ⟦⟨i, m⟩⟧
  map_add' _ _ := (DirectLimit.add_def ..).symm
  map_smul' a m := (smul_mk A f M g i a m).symm

end DirectLimit.VaryingScalar
end
