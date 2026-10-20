@[expose] public section

universe uR uM

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

open scoped ZeroObject

namespace ModuleCat

variable (R : Type uR) [Ring R]

namespace FactorsThroughProjective

variable {R}

lemma zero {M N : ModuleCat.{uM} R} :
    FactorsThroughProjective R (0 : M ⟶ N) := by
  refine ⟨(0 : ModuleCat.{uM} R), inferInstance, 0, 0, ?_⟩
  simp

end FactorsThroughProjective
end ModuleCat
end
