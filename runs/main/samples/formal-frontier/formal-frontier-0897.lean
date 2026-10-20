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

theorem of_map {i j : ι} (hij : i ≤ j) (m : M i) :
    of A f M g j (g i j hij m) = of A f M g i m :=
  (DirectLimit.eq_of_le ⟨i, m⟩ j hij).symm

end DirectLimit.VaryingScalar
end
