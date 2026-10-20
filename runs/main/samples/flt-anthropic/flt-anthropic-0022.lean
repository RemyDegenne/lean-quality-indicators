namespace P2MW.S_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic

set_option autoImplicit false

open scoped TensorProduct

namespace GaloisRep

namespace MultHalfAux

p2m_open

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [Bialgebra R H]

variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

theorem postComp_injective (ψ : A →ₐ[R] B) (hψ : Function.Injective ψ) :
    Function.Injective (postComp (H := H) ψ) := by
  intro f g h
  apply WithConv.ext
  refine AlgHom.ext fun a => hψ ?_
  have := congrArg (fun z => (WithConv.ofConv z) a) h
  exact this

end MultHalfAux
end GaloisRep
end P2MW.S_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
