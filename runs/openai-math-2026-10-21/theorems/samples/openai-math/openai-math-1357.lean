namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4776 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4776 = injectiveMoment H node1649 := by
  calc
    injectiveMoment H raw4776 = injectiveMoment H raw4776step0 := by
      have heq : raw4776step0 = -raw4776 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4776).symm
    injectiveMoment H raw4776step0 = injectiveMoment H raw4776step1 := by
      have heq : raw4776step1 = (fun i j => raw4776step0 (permutation84 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4776step0 permutation84 permutation23
    _ = injectiveMoment H node1649 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
