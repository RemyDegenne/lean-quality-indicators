public section

noncomputable section

open CategoryTheory Limits IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped AdeleGaloisAction TensorProduct

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

section Components

/-- **The semi-local component of an idele at an infinite place** `w` of `K`, its components at
the places of `L` above `w` as a unit of `K_w ⊗[K] L`, as a morphism of representations of
`Aut(L/K)`. -/
def idelesToInfiniteSemilocalUnits (w : InfinitePlace K) :
    idelesRep K L ⟶ infiniteSemilocalUnitsRep L w :=
  idelesToInfiniteIdeles K L ≫ (infiniteIdelesPiIso K L).hom ≫ Rep.piProj _ w

end Components
end TauCeti.ClassFieldTheory
end
end
