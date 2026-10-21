namespace OAI

universe uR uS uT uA

noncomputable section

namespace CirculantHadamard.PrimeCharacterEvaluations

open scoped BigOperators

open CyclicRing

open PrimeComponents CyclotomicRings

@[simp] theorem partialEvaluation_at_root_apply (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2)) :
    partialAtRoot u hu p (partialEvaluation u hu p S x) =
      subsetEvaluation u hu (insert p S) x :=
  congrArg (fun f : Elem GaussianRing (u ^ 2) →+* B u => f x)
    (partialEvaluation_at_root u hu p S)

end CirculantHadamard.PrimeCharacterEvaluations
end
end OAI
