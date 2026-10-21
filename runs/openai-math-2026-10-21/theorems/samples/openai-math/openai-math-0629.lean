namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3126 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3126 = injectiveMoment H node2813 := by
  calc
    injectiveMoment H raw3126 = injectiveMoment H raw3126step0 := by
      have heq : raw3126step0 = -raw3126 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3126).symm
    injectiveMoment H raw3126step0 = injectiveMoment H raw3126step1 := by
      have heq : raw3126step1 = (fun i j => raw3126step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3126step0 permutation100 permutation15
    _ = injectiveMoment H node2813 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
