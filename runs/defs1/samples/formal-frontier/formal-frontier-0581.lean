public section

set_option warningAsError true

open CategoryTheory Topology

namespace CompHausAddCommGrp

universe u

/-- The finite-product topology on finitely supported functions, transported
from the equivalent finite function space. -/
@[instance_reducible, expose]
noncomputable def finiteFinsuppTopology (X : CompHausAddCommGrp.{u})
    (I : Type u) [Finite I] : TopologicalSpace (I →₀ X) :=
  TopologicalSpace.induced Finsupp.equivFunOnFinite inferInstance

end CompHausAddCommGrp
end
