public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti

universe u v w

namespace TopPair

variable {R : Type u} [Ring R]

section Pair

variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)
  (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)] (M : ModuleCat.{max v w} R)

section LongExactSequence

lemma twistedCohomology_exact_subspace (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (P.twistedCohomologyMap_comp_twistedCohomologyδ L k M n m h)).Exact :=
  (P.shortExact_twistedCochainComplexShortComplex L k M).homology_exact₃ n m (by simpa)

end LongExactSequence
end Pair
end TopPair
end
end
