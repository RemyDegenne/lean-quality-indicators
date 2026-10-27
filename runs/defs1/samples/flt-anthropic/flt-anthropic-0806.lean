namespace P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent

attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option Elab.async false

open scoped TensorProduct

open scoped TensorProduct

namespace FltWs11

namespace RED

open HopfAlgebra Algebra.TensorProduct

variable {R : Type} [CommRing R] (K : Type) [CommRing K] [Algebra R K]
  {H : Type} [CommRing H] [HopfAlgebra R H] {H' : Type} [CommRing H'] [HopfAlgebra R H']

noncomputable def bcPair : H ⊗[R] H' →ₐ[R] (K ⊗[R] H) ⊗[K] (K ⊗[R] H') :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : K ⊗[R] H →ₐ[K] (K ⊗[R] H) ⊗[K] (K ⊗[R] H')).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H))
    (((Algebra.TensorProduct.includeRight : K ⊗[R] H' →ₐ[K] (K ⊗[R] H) ⊗[K] (K ⊗[R] H')).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H' →ₐ[R] K ⊗[R] H'))
    (fun x y => Commute.all (S := (K ⊗[R] H) ⊗[K] (K ⊗[R] H')) _ _)

end RED
end FltWs11
end P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent
