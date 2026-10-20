public section

set_option warningAsError true

open CategoryTheory Limits TopologicalSpace Opposite

open AlgebraicGeometry

open TensorProduct

open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

attribute [instance] IsTorsionFree.stalk

theorem isTorsionFree_iff_of_iso {P Q : X.Modules} (e : P ≅ Q) :
    IsTorsionFree P ↔ IsTorsionFree Q :=
  ⟨IsTorsionFree.ofIso e, IsTorsionFree.ofIso e.symm⟩

end AlgebraicGeometry.Scheme.Modules
end
