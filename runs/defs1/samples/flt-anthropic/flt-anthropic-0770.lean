namespace P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain

open scoped TensorProduct

noncomputable section

namespace QuotientFlagProof

universe u v

p2m_reactivate

local notation "L" => AlgebraicClosure ℚ

scoped instance instIsAlgebraicRatL : Algebra.IsAlgebraic ℚ L := AlgebraicClosure.isAlgebraic ℚ

scoped instance instIsAlgClosureRatL : IsAlgClosure ℚ L := AlgebraicClosure.instIsAlgClosure ℚ

scoped instance instNormalRatL : Normal ℚ L := IsAlgClosure.normal ℚ L

scoped instance instIsGaloisRatL : IsGalois ℚ L := IsGalois.mk

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Points

variable {R : Type} [CommRing R] [Algebra R L]

variable {H : Type} [CommRing H] [Algebra R H]

abbrev pfam (S : Set (H →ₐ[R] L)) : S → (H ⧸ J S) →ₗ[R] L := fun g => (pbar S g).toLinearMap

end Points
end QuotientFlagProof
end
end P2MW.S_HopfAlgebra_exists_quotientFlag_of_galoisStableChain
