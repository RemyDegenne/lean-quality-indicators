namespace P2MW.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible

set_option autoImplicit false

open Polynomial Module

universe u v w

noncomputable section

namespace P2mGrp

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

section Pairing

variable (k V)

def tracePairing :
    LinearMap.ker (LinearMap.trace k V) →ₗ[k] Module.Dual k (LinearMap.ker (LinearMap.trace k V)) :=
  LinearMap.mk₂ k
    (fun Y X => LinearMap.trace k V ((Y : Module.End k V) * (X : Module.End k V)))
    (fun Y₁ Y₂ X => by simp [add_mul])
    (fun c Y X => by simp)
    (fun Y X₁ X₂ => by simp [mul_add])
    (fun c Y X => by simp)

end Pairing
end P2mGrp
end
end P2MW.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible
