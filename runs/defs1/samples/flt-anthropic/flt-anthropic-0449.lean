namespace P2MW.S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace VeluOddSurjAux

variable {K : Type*} [Field K]

section Poly

variable [DecidableEq K] (W : WeierstrassCurve K) (S : Finset (K × K))

noncomputable def N : K[X] :=
  X * D S + ∑ P ∈ S, (C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2)) *
    ∏ P' ∈ S.erase P, (X - C P'.1) ^ 2

end Poly
end VeluOddSurjAux
end P2MW.S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed
