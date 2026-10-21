namespace OAI

section

namespace PerfectCompleteness.BucketQuotientAgreement

noncomputable section

open scoped BigOperators Classical

open UniqueGamesTheorem.Foundations.Games

open BucketSampler (F2 Direction Tape)

open PartialTableInverse (definedEquality nonzeroAgreement)

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

theorem probability_collision_eq_expectation {A B Y : Type*}
    [Fintype A] [Fintype B] [Fintype Y]
    (μ : FiniteDistribution A) (f : B → Option Y) (p q : A → B) :
    μ.probability (fun x => TwoResponseCollision.collision f (p x, q x)) =
      μ.expectation (fun x => definedEquality f (p x) (q x)) := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ∃ y, f (p x) = some y ∧ f (q x) = some y <;>
    simp [TwoResponseCollision.collision, definedEquality, h]

end
end PerfectCompleteness.BucketQuotientAgreement
end
end OAI
