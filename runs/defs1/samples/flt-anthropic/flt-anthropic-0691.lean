namespace P2MW.S_WeierstrassCurve_IsCyclicGenKernel_variableChange

set_option autoImplicit false

universe u

open Polynomial

namespace GenKerVCAux

variable {T : Type u} [CommRing T]

noncomputable def hom (d : ℕ) (p A B : T[X]) : T[X] :=
  ∑ i ∈ Finset.range (d + 1), C (p.coeff i) * A ^ i * B ^ (d - i)

end GenKerVCAux
end P2MW.S_WeierstrassCurve_IsCyclicGenKernel_variableChange
