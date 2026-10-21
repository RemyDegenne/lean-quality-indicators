namespace OAI

noncomputable section

namespace StronglyRationalVOA

universe u v

open Filter

namespace HilbertCore

open UniformSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem formalAdjoint {T S : V →ₗ[ℂ] Completion V}
    (h : ∀ v w : V, inner ℂ (T v) (w : Completion V) =
      inner ℂ (v : Completion V) (S w)) :
    (operator T).IsFormalAdjoint (operator S) := by
  intro v w
  obtain ⟨v, rfl⟩ := (equiv V).surjective v
  obtain ⟨w, rfl⟩ := (equiv V).surjective w
  simpa using h v w

end HilbertCore
end StronglyRationalVOA
end
end OAI
