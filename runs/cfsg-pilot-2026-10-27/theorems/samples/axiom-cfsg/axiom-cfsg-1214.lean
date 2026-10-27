public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley

open scoped commutatorElement

variable {τ : Tag}

variable (τ) (K : Type) [Field K]

variable {τ K}

theorem parabolicLevi_le_normalizer
    (J : Set (Fin τ.rank)) {d : ℤ}
    (hd : 1 ≤ d) :
    parabolicLevi τ K J ≤ Subgroup.normalizer (levelRadical τ K J d : Set (ModGL τ K)) :=
  (parabolicLevi_le_parabolicSubgroup J).trans (parabolicSubgroup_le_normalizer J hd)

end CFSG.LieType.Chevalley.EvenOddRadical
end
