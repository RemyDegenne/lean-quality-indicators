namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace P2mWs11RBC

variable {Y : Scheme.{u}}

theorem op_hom_eq {U V : Y.Opens} (i j : op U ⟶ op V) : i = j :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

end P2mWs11RBC
end P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le
