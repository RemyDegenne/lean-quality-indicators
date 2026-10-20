namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime

open scoped MatrixGroups

open Matrix

namespace IharaSchurSL2

section NonsplitTorus

open Polynomial

variable {F : Type*} [Field F] (f : F[X]) (R : Matrix (Fin 2) (Fin 2) F)
  (hR : Polynomial.aeval R f = 0)

theorem evalHom_mk (g : F[X]) : evalHom f R hR (AdjoinRoot.mk f g) = Polynomial.aeval R g :=
  Ideal.Quotient.lift_mk _ _ _

end NonsplitTorus
end IharaSchurSL2
end P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime
