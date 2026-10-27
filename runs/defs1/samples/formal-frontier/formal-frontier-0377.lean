public section

set_option warningAsError true

open CategoryTheory Limits TopologicalSpace Opposite

open AlgebraicGeometry

open TensorProduct

open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A module on a scheme is torsion-free if each stalk is torsion-free over the
corresponding stalk of the structure sheaf. -/
class IsTorsionFree (P : X.Modules) : Prop where
  stalk (x : X) : Module.IsTorsionFree (X.presheaf.stalk x) (P.presheaf.stalk x)

end AlgebraicGeometry.Scheme.Modules
end
