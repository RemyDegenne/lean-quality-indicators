namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw233 = injectiveMoment H node300 := by
  calc
    injectiveMoment H raw233 = injectiveMoment H raw233step0 := by
      have heq : raw233step0 = (fun i j => raw233 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw233 permutation39 permutation3
    _ = injectiveMoment H node300 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
