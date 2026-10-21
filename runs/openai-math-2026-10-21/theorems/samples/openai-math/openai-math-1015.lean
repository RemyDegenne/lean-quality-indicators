namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw112 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw112 = injectiveMoment H raw112step0 := by
      have heq : raw112step0 = -raw112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw112).symm
    injectiveMoment H raw112step0 = injectiveMoment H raw112step1 := by
      have heq : raw112step1 = (fun i j => raw112step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw112step0 permutation9 permutation6
    _ = injectiveMoment H node243 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
