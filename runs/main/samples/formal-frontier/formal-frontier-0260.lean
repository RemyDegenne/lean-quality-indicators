set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

noncomputable section

namespace CorestrictionTransversal

variable {H : Subgroup G} (T : H.RightTransversal)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma changeRep_rightCoset (S : H.RightTransversal) (t : ↥(T : Set G)) :
    RightCosetEquivalence (H : Set G) (changeRep T S t : G) (t : G) := by
  rw [RightCosetEquivalence, rightCoset_eq_iff H]
  rw [← changeFactor_mul_changeRep T S t]
  simp only [mul_inv_cancel_right]
  exact (changeFactor T S t).2

end CorestrictionTransversal
end
end ContinuousCohomology
end
