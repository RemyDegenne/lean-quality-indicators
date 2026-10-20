open scoped HahnSeries

universe u v w

namespace HahnSeries.Nonpositive

public noncomputable section

variable {G : Type u} {K : Type v} {L : Type w}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
  [CommRing K] [CommRing L]

section ScalarExtension

variable [Algebra K L]

/-- Extend the coefficients of a finite-support Hahn series along a coefficient algebra. -/
def finiteSupportScalarExtension :
    FiniteSupportRing (G := G) (K := K) →+*
      FiniteSupportRing (G := G) (K := L) :=
  finiteSupportMap (G := G) (algebraMap K L)

end ScalarExtension
end
end HahnSeries.Nonpositive
