public section

open QuadraticMap

namespace TauCeti

universe u

section Steps

variable {R : Type u} [CommSemiring R] {n : ℕ}

namespace PermutationStep

theorem to_reflTransGen_binaryStep {w w' : Fin n → Rˣ} (h : PermutationStep w w') :
    Relation.ReflTransGen BinaryStep w w' := by
  rw [PermutationStep] at h
  obtain ⟨σ, hσ⟩ := h
  have hperm : ∀ (τ : Equiv.Perm (Fin n)) (v : Fin n → Rˣ),
      Relation.ReflTransGen BinaryStep v (v ∘ τ) := by
    intro τ
    induction τ using Equiv.Perm.swap_induction_on with
    | one =>
        intro v
        simpa using (Relation.ReflTransGen.refl :
          Relation.ReflTransGen BinaryStep v v)
    | swap_mul τ i j hij ih =>
        intro v
        refine (Relation.ReflTransGen.single (BinaryStep.swap v hij)).trans ?_
        simpa [Function.comp_def] using ih (v ∘ Equiv.swap i j)
  convert hperm σ w using 1
  funext i
  exact hσ i

end PermutationStep
end Steps
end TauCeti
end
