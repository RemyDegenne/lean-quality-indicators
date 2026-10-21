namespace OAI

noncomputable section

namespace TotientAsymptotic

lemma ford_first_two_factorization {n : ℕ} (hn : 0 < n) :
    n=fordPrime n 0*fordPrime n 1*fordCofactor n 2 := by
  calc
    n = fordCofactor n 0 := (fordCofactor_zero hn).symm
    _ = _ := by
      rw [fordCofactor_step n 0,fordCofactor_step n 1]
      simp only [Nat.reduceAdd]
      ring

end TotientAsymptotic
end
end OAI
