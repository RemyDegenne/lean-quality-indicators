public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllObj

variable {B : Scheme.{u}}

variable {X Y Z : EllObj B}

variable (B) in
/-- The **forgetful functor** `Ell/B ⥤ Sch/B`, sending an elliptic curve `E` over a `B`-scheme `S`
to `S`, and an arrow of `Ell/B` to its morphism of bases. -/
@[expose, simps]
def forget : EllObj B ⥤ Over B where
  obj X := Over.mk X.structureMap
  map f := Over.homMk f.base f.base_structureMap

end EllObj
end TauCeti.AlgebraicGeometry
end
