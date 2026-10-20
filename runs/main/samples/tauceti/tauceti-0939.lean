public section

noncomputable section

open Polynomial NumberField Ideal

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
  (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
  (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)

include hmin hgen

theorem dedekindCubic_primesOver_two_eq :
    (span {(2 : ℤ)}).primesOver (𝓞 K) =
      {dedekindPrimeOne (dedekindCubic_relation hmin),
        dedekindPrimeTwo (dedekindCubic_relation hmin),
        dedekindPrimeThree (dedekindCubic_relation hmin)} := by
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
  · simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨(isMaximal_dedekindPrimeOne hmin hgen).isPrime, liesOver_dedekindPrimeOne hmin hgen⟩,
      ⟨(isMaximal_dedekindPrimeTwo hmin hgen).isPrime, liesOver_dedekindPrimeTwo hmin hgen⟩,
      ⟨(isMaximal_dedekindPrimeThree hmin hgen).isPrime, liesOver_dedekindPrimeThree hmin hgen⟩⟩
  · rw [ncard_dedekindPrimes hmin hgen, ← dedekindCubic_finrank_eq_three hmin hgen,
      ← RingOfIntegers.rank K]
    exact RamificationInertia.ncard_primesOver_le_finrank _

end TauCeti.NumberField
end
end
