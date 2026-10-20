@[expose] public section

universe uR uM

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

open scoped ZeroObject

namespace ModuleCat

variable (R : Type uR) [Ring R]

namespace FactorsThroughProjective

variable {R}

lemma of_projective_source {M N : ModuleCat.{uM} R} [CategoryTheory.Projective M]
    (f : M ⟶ N) : FactorsThroughProjective R f :=
  ⟨M, inferInstance, 𝟙 M, f, by simp⟩

end FactorsThroughProjective
end ModuleCat
end
