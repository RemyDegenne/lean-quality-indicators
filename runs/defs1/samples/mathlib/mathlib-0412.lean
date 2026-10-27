@[expose] public section

open KaehlerDifferential

namespace Algebra.Extension

universe w v u

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The first homology of the naive cotangent complex of `P.extendScalars` is
linearly equivalent to that of `S` over `P.Ring`. -/
@[simps! toLinearMap]
noncomputable
def h1CotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    P.extendScalars.H1Cotangent ≃ₗ[S] H1Cotangent P.Ring S :=
  Extension.H1Cotangent.equiv
    (.ofAlgHom (Algebra.ofId _ _) (by ext)) P.extendScalars.defaultHom

end Algebra.Extension
end
