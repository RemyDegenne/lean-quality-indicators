namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp

open scoped BigOperators

open Filter

lemma palindrome_probability_step (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card (d+1)) :
    PairRouting.tupleProbability (palindromePerm (d+1)) e f =
    finiteMean (fun ω : BenesCoins d × BenesCoins d =>
      finiteMean (fun coins : (Card d → Bool) × (Card d → Bool) =>
        if ∀ i, PairRouting.sandwich coins.1 coins.2 (fun b => if b then palindromePerm d ω.2 else palindromePerm d ω.1)
          ((e.trans (headTailEquiv d).toEmbedding) i) = ((f.trans (headTailEquiv d).toEmbedding) i)
        then (1:ℝ) else 0)) := by
  classical
  rw [PairRouting.tupleProbability,finiteMean_equiv (benesStepEquiv d),finiteMean_prod]
  have hp (b : Bool) (p q : BenesCoins d) :
      palindromePerm d (if b then p else q) = (if b then palindromePerm d p else palindromePerm d q) := by
    cases b <;> rfl
  simp only [palindrome_matches_step,hp]

end Thorp
end ThorpNine.Smoothing
end OAI
