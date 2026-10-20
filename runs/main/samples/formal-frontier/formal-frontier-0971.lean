public section

open Function Set

open CategoryTheory

universe u v w

namespace Module

variable {R : Type u} [CommRing R]

section CanonicalRealization

theorem rankIdempotent_eq_sum_locallyConstantRankFiberIdempotent
    (f : LocallyConstant (PrimeSpectrum R) ℕ)
    (i : Fin (ModuleCat.FiniteProjective.rankBound f)) :
    ModuleCat.FiniteProjective.rankIdempotent f i =
      ∑ j : locallyConstantRankFiberIndex f,
        if i.1 < locallyConstantRankFiberRank f j then
          locallyConstantRankFiberIdempotent f j else 0 := by
  classical
  calc
    ModuleCat.FiniteProjective.rankIdempotent f i =
        ModuleCat.FiniteProjective.rankIdempotent f i * 1 := by rw [mul_one]
    _ = ModuleCat.FiniteProjective.rankIdempotent f i *
        (∑ j : locallyConstantRankFiberIndex f,
          locallyConstantRankFiberIdempotent f j) := by
      rw [rankFiberIdempotents_complete R
        (ModuleCat.FiniteProjective.ofLocallyConstantRank R f) |>.complete]
    _ = ∑ j : locallyConstantRankFiberIndex f,
        ModuleCat.FiniteProjective.rankIdempotent f i *
          locallyConstantRankFiberIdempotent f j := by rw [Finset.mul_sum]
    _ = _ := Finset.sum_congr rfl fun j _ ↦
      rankIdempotent_mul_locallyConstantRankFiberIdempotent f i j

end CanonicalRealization
end Module
end
