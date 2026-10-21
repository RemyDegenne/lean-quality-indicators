namespace OAI

noncomputable section

open CategoryTheory

open scoped BigOperators

open CategoryTheory Finsupp

open CategoryTheory Finsupp MonoidalCategory

open scoped BigOperators Matrix

open scoped Matrix

open scoped MonoidAlgebra

namespace CoboundaryExpanders.CosetModules

section

universe u

variable {k G : Type u} [Field k] [Group G]

theorem projective_permutation_of_invertible_order (H : Subgroup G)
    [Finite H] [NeZero (Nat.card H : k)] : Projective (permutation (k := k) H) := by
  let A := Rep.trivial k H k
  let M := Rep.toModuleMonoidAlgebra.obj A
  let : Module.Projective (MonoidAlgebra k H) M :=
    Module.projective_of_isSemisimpleRing _ _
  have : Projective M := inferInstance
  have : Projective A :=
    Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective A
      (inferInstance : Projective M)
  exact projective_permutation H

end
end CoboundaryExpanders.CosetModules
end
end OAI
