namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover

set_option autoImplicit false

set_option maxHeartbeats 1600000

universe v v' u

p2m_open

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

namespace ObjGlue

p2m_open

section Opens

variable {Y : Scheme.{u}} {ι : Type u} (U : ι → Y.Opens)

variable (D : (MOD.{u}).DescentData (incl U))

noncomputable def castComp {X₀ X₁ X₂ : Scheme.{u}} (e : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (a' : X₀ ⟶ X₂) [IsOpenImmersion e]
    [IsOpenImmersion a] [IsOpenImmersion a'] (w : e ≫ a = a') (M : X₂.Modules) :
    (restrictFunctor a').obj M ⟶ (restrictFunctor e).obj ((restrictFunctor a).obj M) :=
  (restrictFunctorCongr w.symm).hom.app M ≫ (restrictFunctorComp e a).hom.app M

end Opens
end ObjGlue
end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
