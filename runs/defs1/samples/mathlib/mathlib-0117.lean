@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace Cylinder

variable {X Y : C}

namespace LeftHomotopy

section

variable [CategoryWithWeakEquivalences C] (P : Cylinder X)

variable {P} in
/-- If `f` and `g` are homotopic relative to a cylinder `P`, then `g` and `f`
are homotopic relative to `P.symm`. -/
abbrev symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f :=
  Precylinder.LeftHomotopy.symm h

end
end LeftHomotopy
end Cylinder
end HomotopicalAlgebra
end
