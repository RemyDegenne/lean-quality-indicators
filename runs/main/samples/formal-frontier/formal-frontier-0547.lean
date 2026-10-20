public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

lemma i_retract_of_p_eq_zero {b : B} (hb : S.p b = 0) :
    S.i (S.retract b) = b := by
  rcases (S.exact b).1 hb with ⟨a, rfl⟩
  rw [retract_i_apply]

end TopologicallySplitShortExact
end ContinuousCohomology
end
