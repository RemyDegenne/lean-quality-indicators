namespace OAI

noncomputable section

namespace PolycyclicRecognition

open scoped MonoidAlgebra

variable {R G : Type} [CommRing R] [Group G] {n : ℕ}

theorem finite_normalizedControlledTuples (S : Set G) (hS : S.Finite) :
    {x : Fin (n + 1) → G | IsControlledTuple S x ∧ x 0 = 1}.Finite := by
  apply (Set.Finite.pi' (fun _ : Fin (n + 1) => hS)).subset
  intro x hx i
  simpa only [hx.2, inv_one, one_mul] using hx.1 0 i

end PolycyclicRecognition
end
end OAI
