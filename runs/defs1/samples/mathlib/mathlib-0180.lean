@[expose] public section

universe u

open Algebra IsCyclotomicExtension Polynomial NumberField

open scoped Cyclotomic Nat

variable {p k n : ℕ} {K : Type u} [Field K] {ζ : K} [hp : Fact p.Prime]

section PowerBasis

open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable [CharZero K]

set_option backward.isDefEq.respectTransparency.types false in
/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
noncomputable def subOneIntegralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasisOfPrimePow.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
    simp [RingOfIntegers.ext_iff, integralPowerBasisOfPrimePow_gen, toInteger])

end IsPrimitiveRoot
end PowerBasis
end
