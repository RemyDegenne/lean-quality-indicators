namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6588 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6588 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw6588 = injectiveMoment H raw6588step0 := by
      have heq : raw6588step0 = raw6588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6588).symm
    injectiveMoment H raw6588step0 = injectiveMoment H raw6588step1 := by
      have heq : raw6588step1 = -raw6588step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6588step0).symm
    injectiveMoment H raw6588step1 = injectiveMoment H raw6588step2 := by
      have heq : raw6588step2 = (fun i j => raw6588step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6588step1 permutation25 permutation3
    _ = injectiveMoment H node244 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
