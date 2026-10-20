@[expose] public section

open scoped TensorProduct

universe u v

attribute [instance]
  FormallyEtale.subsingleton_kaehlerDifferential FormallyEtale.subsingleton_h1Cotangent

attribute [instance] formallyEtale finitePresentation

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/--
A ring homomorphism `R →+* A` is formally étale if it is formally unramified and formally smooth.
See `Algebra.FormallyEtale`.
-/
@[algebraize Algebra.FormallyEtale]
def FormallyEtale (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallyEtale R S

end RingHom
end
