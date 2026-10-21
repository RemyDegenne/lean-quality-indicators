namespace OAI

noncomputable section

namespace PolycyclicRecognition

open CategoryTheory

attribute [local instance 2000] Rep.hV2 Rep.instLinear

variable {G : Type} [Group G]

namespace SequentialRepresentationDiagram

variable (A : ℕ → Rep.{0} ℤ G) (f : ∀ n, A n ⟶ A (n + 1))

@[simp]
theorem ofConsecutive_map_step (i : ℕ) :
    (ofConsecutive A f).map i (i + 1) (Nat.le_succ i) = f i := by
  change consecutiveMap A f i (i + 1) (Nat.le_succ i) = f i
  rw [consecutiveMap_step A f i i le_rfl, consecutiveMap_self, Category.id_comp]

end SequentialRepresentationDiagram
end PolycyclicRecognition
end
end OAI
