namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3713 = injectiveMoment H node2072 := by
  calc
    injectiveMoment H raw3713 = injectiveMoment H raw3713step0 := by
      have heq : raw3713step0 = (fun i j => raw3713 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3713 permutation33 permutation10
    _ = injectiveMoment H node2072 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
