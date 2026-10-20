public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

section MayerVietoris

variable (U V : Opens X)

variable {U V}

theorem subsingleton_cohomologyOn_sup_succ (n : ℕ)
    (hInter : Subsingleton (cohomologyOn M n (U ⊓ V)))
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Subsingleton (cohomologyOn M (n + 1) (U ⊔ V)) :=
  (Opens.mayerVietorisSquare U V).subsingleton_H'_X₄
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n (n + 1) rfl hInter hU hV

end MayerVietoris
end Scheme.Modules
end
end AlgebraicGeometry
end TauCeti
end
