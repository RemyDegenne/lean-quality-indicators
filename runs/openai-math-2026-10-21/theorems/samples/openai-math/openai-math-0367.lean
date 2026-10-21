namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1110 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1110 = injectiveMoment H node1238 := by
  calc
    injectiveMoment H raw1110 = injectiveMoment H raw1110step0 := by
      have heq : raw1110step0 = raw1110.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1110).symm
    injectiveMoment H raw1110step0 = injectiveMoment H raw1110step1 := by
      have heq : raw1110step1 = -raw1110step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1110step0).symm
    injectiveMoment H raw1110step1 = injectiveMoment H raw1110step2 := by
      have heq : raw1110step2 = (fun i j => raw1110step1 (permutation9 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1110step1 permutation9 permutation24
    _ = injectiveMoment H node1238 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
