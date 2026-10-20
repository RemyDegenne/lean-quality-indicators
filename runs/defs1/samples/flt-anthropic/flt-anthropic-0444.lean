namespace P2MW.S_FinFlatHopf_exists_left_integral_frobenius

set_option Elab.async false

noncomputable section

namespace FinFlatHopf

open Coalgebra HopfAlgebra WithConv LinearMap Module

p2m_open_scoped

namespace S2

variable {B : Type} [CommRing B] {H : Type} [CommRing H] [HopfAlgebra B H]

section FiniteBasis

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι B H)

section Sco

variable (hSco : ∀ (a : H) {ι𝓡 : Type} (𝓡 : Coalgebra.Repr B a ι𝓡),
    comul (R := B) (antipode B a) =
      ∑ i ∈ 𝓡.index, antipode B (𝓡.right i) ⊗ₜ[B] antipode B (𝓡.left i))

def antipodeRepr {a : H} {ι𝓡 : Type} (𝓡 : Coalgebra.Repr B a ι𝓡) :
    Coalgebra.Repr B (antipode B a) ι𝓡 where
  index := 𝓡.index
  left j := antipode B (𝓡.right j)
  right j := antipode B (𝓡.left j)
  eq := (hSco a 𝓡).symm

end Sco
end FiniteBasis
end S2
end FinFlatHopf
end
end P2MW.S_FinFlatHopf_exists_left_integral_frobenius
