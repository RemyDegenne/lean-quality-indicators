namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9020 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw9020 = injectiveMoment H raw9020step0 := by
      have hz : ∀ j, raw9020 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw9020step0 = (fun i j => raw9020 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9020 permutation21 hz
    injectiveMoment H raw9020step0 = injectiveMoment H raw9020step1 := by
      have hz : ∀ j, raw9020step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw9020step1 = (fun i j => raw9020step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9020step0 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
