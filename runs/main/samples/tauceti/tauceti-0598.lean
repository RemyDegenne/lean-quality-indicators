public section

open Module

namespace QuadraticMap

open TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V}

theorem IsTotallyIsotropic.finrank_le_wittIndex (hQ : Q.Nondegenerate)
    (hW : Q.IsTotallyIsotropic W) :
    finrank K W ≤ RegularFormClass.wittIndex (formClass Q hQ) := by
  obtain ⟨W', hle, -, hW'⟩ := hW.exists_le_finrank_eq_wittIndex hQ
  exact hW' ▸ Submodule.finrank_mono hle

end QuadraticMap
end
