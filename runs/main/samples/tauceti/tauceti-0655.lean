public section

namespace TauCeti

open CategoryTheory PathAlgebra

universe u v w t

section Morphism

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

variable {M N P : Type t} [AddCommGroup M] [Module k M] [Module (pathAlgebra k Q) M]
  [IsScalarTower k (pathAlgebra k Q) M] [AddCommGroup N] [Module k N]
  [Module (pathAlgebra k Q) N] [IsScalarTower k (pathAlgebra k Q) N] [AddCommGroup P]
  [Module k P] [Module (pathAlgebra k Q) P] [IsScalarTower k (pathAlgebra k Q) P]

@[simp]
theorem quiverRepHomOfModule_comp (f : M →ₗ[pathAlgebra k Q] N) (g : N →ₗ[pathAlgebra k Q] P) :
    quiverRepHomOfModule k Q (g.comp f)
      = quiverRepHomOfModule k Q f ≫ quiverRepHomOfModule k Q g := by
  refine NatTrans.ext (funext fun v ↦ ?_)
  change Q at v
  rw [quiverRepHomOfModule_app, vertexComponentMap_comp]
  exact ModuleCat.ofHom_comp (vertexComponentMap k f v) (vertexComponentMap k g v)

end Morphism
end TauCeti
end
