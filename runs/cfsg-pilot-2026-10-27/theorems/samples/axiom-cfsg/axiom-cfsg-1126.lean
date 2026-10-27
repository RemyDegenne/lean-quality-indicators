public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelUnpack

open CFSG.Open

open CFSG.Blueprint (LieModel)

theorem not_dvd_card_scalars_statedOmega_quadOdd {n : ℕ} {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf
      (StatedOmega (StatedQuadOdd n K))) :=
  StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedOmega (StatedQuadOdd n K)) hp
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h))
    (fun c hc => CFSG.GroupTheory.WeirSylow.sq_eq_one_of_scalar_mem_statedOmega_quadOdd c hc)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelUnpack
end
