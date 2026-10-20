@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

section ker

open IdealSheafData

variable {Y Z : Scheme.{u}}

/-- The kernel of a morphism,
defined as the largest (quasi-coherent) ideal sheaf contained in the component-wise kernel.
This is usually only well-behaved when `f` is quasi-compact. -/
def Hom.ker (f : X.Hom Y) : IdealSheafData Y :=
  ofIdeals fun U ↦ RingHom.ker (f.app U).hom

end ker
end AlgebraicGeometry.Scheme
end
