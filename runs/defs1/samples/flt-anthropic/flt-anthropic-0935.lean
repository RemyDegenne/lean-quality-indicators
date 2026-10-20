namespace P2MW.S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt

set_option autoImplicit false

p2m_open

open scoped Manifold Topology Classical

noncomputable section

namespace AutomorphicForm

p2m_open

namespace MaassDictionary

section Transport

variable (F : Type) [Field F] [NumberField F]

def rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm he (rotSO θ)

end Transport
end MaassDictionary
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt
