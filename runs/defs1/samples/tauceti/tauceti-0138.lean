public section

open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

open _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The monoid of nonzero integral ideals whose absolute norm is coprime to the modulus formed by
the prime discriminants in `t`. The prime-discriminant hypotheses needed for nonvanishing are
separate arguments to `genusCharFunCoprimeIdealHom`. -/
def genusCharFunCoprimeIdealSubmonoid (t : Finset ℤ) :
    Submonoid ((Ideal (𝓞 K))⁰) where
  carrier := {I | IsCoprime (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P)}
  one_mem' := by
    -- Unfold the carrier predicate to expose the ideal norm's monoid-one law.
    change IsCoprime (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P)
    rw [map_one]
    exact isCoprime_one_left
  mul_mem' := by
    intro I J hI hJ
    have hI' : IsCoprime (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P) := by
      simpa only [Set.mem_ofPred_eq] using hI
    have hJ' : IsCoprime (Ideal.absNorm (J : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P) := by
      simpa only [Set.mem_ofPred_eq] using hJ
    simpa only [Set.mem_ofPred_eq, Submonoid.coe_mul, map_mul, Nat.cast_mul] using
      hI'.mul_left hJ'

end TauCeti.Multiquadratic
end
