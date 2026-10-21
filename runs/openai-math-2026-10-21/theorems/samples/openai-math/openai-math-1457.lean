namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6520 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6520 = injectiveMoment H node157 := by
  calc
    injectiveMoment H raw6520 = injectiveMoment H raw6520step0 := by
      have heq : raw6520step0 = raw6520.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6520).symm
    injectiveMoment H raw6520step0 = injectiveMoment H raw6520step1 := by
      have heq : raw6520step1 = -raw6520step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6520step0).symm
    injectiveMoment H raw6520step1 = injectiveMoment H raw6520step2 := by
      have heq : raw6520step2 = (fun i j => raw6520step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6520step1 permutation31 permutation4
    _ = injectiveMoment H node157 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
