@[expose] public section

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]

variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

open ContinuousLinearMap

namespace Unitization

variable {𝕜 A}

variable [RegularNormedAlgebra 𝕜 A]

variable (𝕜 A)

variable {𝕜 A}

section Aux

attribute [local instance] Unitization.normedRingAux

attribute [local instance] Unitization.normedAlgebraAux

open Bornology Filter

open scoped Uniformity Topology

theorem cobounded_eq_aux :
    @cobounded _ (Bornology.induced <| addEquiv 𝕜 A) = cobounded (Unitization 𝕜 A) :=
  le_antisymm lipschitzWith_addEquiv.comap_cobounded_le
    antilipschitzWith_addEquiv.tendsto_cobounded.le_comap

end Aux
end Unitization
end
