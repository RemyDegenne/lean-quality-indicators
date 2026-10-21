namespace OAI

noncomputable section

open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma quotientEquiv_transition (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) S h
      (quotientEquiv I n x) =
    quotientEquiv I m (AdicCompletion.transitionMap I S h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [quotientEquiv_mk]
      exact (quotientEquiv_mk I m s).symm

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar
end
end OAI
