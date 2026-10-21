namespace OAI

noncomputable section

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

namespace Contingency.PaddedGraph

noncomputable section

open FiniteChain

variable {m n a c' : ℕ} (U L d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // U ≤ r i}) (ec : Fin c' ≃ {j // U ≤ c j}) (i₀ : Fin a) (j₀ : Fin c')
    (hd : 1 ≤ d) (hmn : m*n ≤ d)

local notation "Comp" => fun X : GraphState U r c => Completion U L r c (graphUnderlying U r c X)

local instance unpaddingTrialCompFintype (X : GraphState U r c) : Fintype (Comp X) := Fintype.ofFinite _

local instance unpaddingTrialTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

theorem implementedTrial_bits (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X₀ : GraphState U r c) (t : ℕ) :
    (implementedTrial U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).bits=t*(Nat.clog 2 (32*d^2)+S)+S := by
  classical
  simp only [implementedTrial,DyadicLaw.map_bits,DyadicLaw.sigma_bits,implementedWalk,DyadicLaw.walk_bits]

end
end Contingency.PaddedGraph
end
end OAI
