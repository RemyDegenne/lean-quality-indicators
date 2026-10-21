namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2353 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2353 = injectiveMoment H node1803 := by
  calc
    injectiveMoment H raw2353 = injectiveMoment H raw2353step0 := by
      have heq : raw2353step0 = (fun i j => raw2353 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2353 permutation34 permutation9
    _ = injectiveMoment H node1803 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
