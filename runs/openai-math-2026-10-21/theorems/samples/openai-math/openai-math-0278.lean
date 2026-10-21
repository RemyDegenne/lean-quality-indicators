namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3154 = injectiveMoment H node504 := by
  calc
    injectiveMoment H raw3154 = injectiveMoment H raw3154step0 := by
      have heq : raw3154step0 = raw3154.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3154).symm
    injectiveMoment H raw3154step0 = injectiveMoment H raw3154step1 := by
      have heq : raw3154step1 = -raw3154step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3154step0).symm
    injectiveMoment H raw3154step1 = injectiveMoment H raw3154step2 := by
      have heq : raw3154step2 = (fun i j => raw3154step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3154step1 permutation21 permutation17
    _ = injectiveMoment H node504 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
