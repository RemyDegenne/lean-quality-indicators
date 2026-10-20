public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

lemma retract_eq_on_ker (r : B →L[k] A) (hr : ∀ a, r (S.i a) = a)
    {b : B} (hb : S.p b = 0) :
    r b = S.retract b := by
  rw [← S.i_retract_of_p_eq_zero hb, hr, retract_i_apply]

end TopologicallySplitShortExact
end ContinuousCohomology
end
