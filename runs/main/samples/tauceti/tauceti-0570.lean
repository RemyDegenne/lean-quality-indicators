public section

open Module

namespace QuadraticMap

open TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V}

theorem IsTotallyIsotropic.exists_le_finrank_eq_wittIndex (hQ : Q.Nondegenerate)
    (hW : Q.IsTotallyIsotropic W) :
    ∃ W' : Submodule K V, W ≤ W' ∧ Q.IsTotallyIsotropic W' ∧
      finrank K W' = RegularFormClass.wittIndex (formClass Q hQ) := by
  obtain ⟨W', hle, hW'⟩ := exists_maximal_ge_of_wellFoundedGT _ W hW
  exact ⟨W', hle, hW'.prop, QuadraticForm.finrank_eq_wittIndex_of_maximal Q hQ hW'⟩

end QuadraticMap
end
