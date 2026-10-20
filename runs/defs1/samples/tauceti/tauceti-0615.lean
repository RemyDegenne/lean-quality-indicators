public section

namespace TauCeti

open Multiplicative

attribute [local instance] trivialMulDistribMulAction

/-- **The class of the extension `ℤ/4` in `H²(ℤ/2, 𝔽₂)`**: the class of the profinite extension
`1 → ℤ/2 → ℤ/4 → ℤ/2 → 1` in Mathlib's continuous cohomology of the trivial
`𝔽₂`-representation of `ℤ/2`. -/
noncomputable def zmodFourExtensionClass : cohomFp 2 (Multiplicative (ZMod 2)) 2 :=
  -- The trivial action of the discrete group `ℤ/2` on the discrete group `ℤ/2` is continuous; its
  -- scalar multiplication is named, because `ℤ/2` also acts on itself by multiplication.
  ProfiniteGroupExtension.zmodFour.cohomFpClass
    (hcont := @ContinuousSMul.mk _ _ (trivialMulDistribMulAction _ _).toMulAction.toSMul _ _
      continuous_of_discreteTopology)
    trivialMulDistribMulAction_smul

end TauCeti
end
