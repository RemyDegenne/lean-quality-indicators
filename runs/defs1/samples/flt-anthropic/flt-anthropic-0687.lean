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

noncomputable def T (i j : ι) (O : Y.Opens) (hi : O ≤ U i) (hj : O ≤ U j) (V : Y.Opens) (hV : V ≤ O)
    (x : Γ(Dobj U D i, (U i).ι ⁻¹ᵁ V)) : Γ(Dobj U D j, (U j).ι ⁻¹ᵁ V) :=
  (Dobj U D j).presheaf.map (homOfLE (T_le_out U j O hj V hV)).op
    ((τ U D i j O hi hj).hom.app (O.ι ⁻¹ᵁ V)
      ((Dobj U D i).presheaf.map (homOfLE (T_le_in U i O hi V)).op x))

end Opens
end ObjGlue
end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
