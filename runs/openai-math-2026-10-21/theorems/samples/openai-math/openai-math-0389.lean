namespace OAI

noncomputable section

open scoped BigOperators

open Finset

namespace KServer.CausalSide

open AdaptiveMinimization SideFamilies

attribute [local instance] Classical.propDecidable Classical.decEq

variable {J R Ω : Type} [Fintype J] [Fintype R]

lemma model_update (c : ℝ) (d : Input J R) (p : J × R → ℝ) (D : ℝ) (a : J → ℝ) :
    (model c).update d p D a=(SideFamilies.family c).update d.data p D a := rfl

end KServer.CausalSide
end
end OAI
