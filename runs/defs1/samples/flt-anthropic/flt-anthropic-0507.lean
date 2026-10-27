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

noncomputable def proj (k : ι) : glued U D ⟶ P U D k :=
  ⟨PresheafOfModules.homMk (M₁ := (glued U D).val) (M₂ := (P U D k).val) (projAb U D k) (fun W r s => rfl)⟩

end Opens
end ObjGlue
end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
