public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn
  HeckeRing.GL2

open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace TauCeti

variable {N Q R : ℕ} [NeZero N] {k : ℤ}

namespace Nat.IsExactDivisor

/-- **The normalized Atkin–Lehner operator on the trivial-nebentypus space** `S_k(N, 1)`: the
operator `𝒲_Q` of `S_k(Γ₀(N))`, transported along the identification
`cuspFormCharSpaceOneEquiv : S_k(N, 1) ≃ S_k(Γ₀(N))`. -/
noncomputable def normalizedAtkinLehnerCharCuspOneEnd (h : Q ∥ N) (k : ℤ) :
    Module.End ℂ (cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :=
  (cuspFormCharSpaceOneEquiv N k).symm.conj (h.normalizedAtkinLehnerOperatorCusp k)

end Nat.IsExactDivisor
end TauCeti
end
