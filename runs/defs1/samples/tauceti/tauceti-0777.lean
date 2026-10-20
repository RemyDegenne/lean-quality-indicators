public section

open Module

universe u v w

namespace CliffordAlgebra

open TauCeti

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  (Q : QuadraticForm R M)

/-- The basis of `CliffordAlgebra Q` attached to a basis `b` of `M`, indexed by the finite subsets
of the index set of `b`, obtained by transporting Mathlib's basis of `ExteriorAlgebra R M` along
`CliffordAlgebra.equivExterior`.

Its elements are not products of generators by construction; see the implementation notes.

`@[expose]` because the characteristic equation `basis_apply` below is a public theorem whose proof
has to unfold this definition. -/
@[expose] noncomputable def basis {I : Type w} [LinearOrder I] (b : Basis I R M) :
    Basis (Finset I) R (CliffordAlgebra Q) :=
  b.ExteriorAlgebra.map (equivExterior Q).symm

end CommRing
end CliffordAlgebra
end
