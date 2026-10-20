public section

namespace TauCeti.freeProP

open Subgroup Submodule

open scoped commutatorElement

universe u

variable {p : ℕ} {X : Type u} {m : ℕ}

section Delta

variable [Fact p.Prime] [Finite X] [LinearOrder X]

variable (p X) in
/-- **The basis-modification map `δ`**, for `m ≥ 1`: the `𝔽_p`-bilinear map
`gr_1(F) → gr_m(F)^X → gr_{m+1}(F)` sending a class `ρ ∈ gr_1(F)` and a family `v` to

  `δ_ρ(v) = Σ_i c_i (π v_i + (p choose 2) • [v_i, ξ_i]) + Σ_{i<k} a_{ik} ([v_i, ξ_k] - [v_k, ξ_i])`

where `c_i` and `a_{ik}` are the coordinates of `ρ` in the standard basis
`TauCeti.freeProP.degreeOneBasis` of `gr_1(F)`, that is
`ρ = Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]` with `ξ_i ∈ gr_0(F)` the class of `x_i`. It is
defined by its values on that basis
(`TauCeti.freeProP.basisModificationDelta_degreeOneBasis_inl`,
`TauCeti.freeProP.basisModificationDelta_degreeOneBasis_inr`), and its value at a general `ρ` is
`TauCeti.freeProP.basisModificationDelta_apply`. For a relator `r ∈ λ_1(F)` with class `ρ`, and
`w : X → λ_m(F)` with classes `v_i = ω_i`, `δ_ρ(v)` is the class in `gr_{m+1}(F)` of
`r⁻¹ * θ_w r`, the amount by which the basis modification `θ_w` moves `r`
(`TauCeti.freeProP.gradedMk_inv_mul_basisModification`). -/
noncomputable def basisModificationDelta (hm : 1 ≤ m) :
    gradedPiece p (freeProP p X) 1 →ₗ[ZMod p]
      (X → gradedPiece p (freeProP p X) m) →ₗ[ZMod p] gradedPiece p (freeProP p X) (m + 1) :=
  (degreeOneBasis p X).constr (ZMod p) <| Sum.elim
    (fun i ↦ ((gradedPowAddMonoidHom p (freeProP p X) hm).toZModLinearMap p +
        p.choose 2 • (gradedBracketLinear p (freeProP p X) m 0).flip
          (gradedMkZero p (freeProP p X) (of i))) ∘ₗ
      LinearMap.proj i)
    fun ij ↦ (gradedBracketLinear p (freeProP p X) m 0).flip
        (gradedMkZero p (freeProP p X) (of ij.1.2)) ∘ₗ LinearMap.proj ij.1.1 -
      (gradedBracketLinear p (freeProP p X) m 0).flip
        (gradedMkZero p (freeProP p X) (of ij.1.1)) ∘ₗ LinearMap.proj ij.1.2

end Delta
end TauCeti.freeProP
end
