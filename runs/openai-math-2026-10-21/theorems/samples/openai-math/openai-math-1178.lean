namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section

open scoped BigOperators Classical

open MvPolynomial

noncomputable section

open scoped Classical BigOperators

namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_4} [Field Q] [Fintype Q] {n q : ℕ}

theorem sum_complement_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q) (hn : 0 < n)
    (O : Finset (Fin n → Q)) (hO : O ⊆ simplexPoints a n ((q - 2) / 2)) :
    ∑ v ∈ Finset.univ \ O, gramColumn a ((q - 2) / 2) O v = -1 := by
  have h := Finset.sum_sdiff (f := gramColumn a ((q - 2) / 2) O) (Finset.subset_univ O)
  rw [sum_holes_gram a O hO, sum_all_gram a hq hn O] at h
  exact eq_neg_of_add_eq_zero_left h

end KaplanskyCounterexample.PolynomialPairing
end
end
end OAI
