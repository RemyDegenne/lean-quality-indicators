namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1077 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1077 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw1077 = injectiveMoment H raw1077step0 := by
      have heq : raw1077step0 = raw1077.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1077).symm
    injectiveMoment H raw1077step0 = injectiveMoment H raw1077step1 := by
      have heq : raw1077step1 = (fun i j => raw1077step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1077step0 permutation30 permutation24
    _ = injectiveMoment H node914 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
