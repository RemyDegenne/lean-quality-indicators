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

theorem pairing_smul_right
    (a : ScalarLimit A f)
    (m : DirectLimit M (fun i j hij ↦ g i j hij))
    (n : DirectLimit N (fun i j hij ↦ h i j hij)) :
    pairing A f M g N h m (a • n) =
      a • pairing A f M g N h m n := by
  induction a using DirectLimit.induction with
  | _ i a =>
    induction m using DirectLimit.induction with
    | _ j m =>
      induction n using DirectLimit.induction with
      | _ l n =>
        obtain ⟨k, hik, hjk, hlk⟩ := directed_of₃ (· ≤ ·) i j l
        rw [DirectLimit.eq_of_le ⟨i, a⟩ k hik,
          DirectLimit.eq_of_le ⟨j, m⟩ k hjk,
          DirectLimit.eq_of_le ⟨l, n⟩ k hlk,
          smul_mk, pairing_mk, pairing_mk, tensorOf_apply, tensorOf_apply, smul_mk,
          TensorProduct.tmul_smul]

end TensorProduct
end DirectLimit.VaryingScalar
end
