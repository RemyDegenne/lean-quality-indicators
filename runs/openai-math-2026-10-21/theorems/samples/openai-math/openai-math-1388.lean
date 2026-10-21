namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3087 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3087 = injectiveMoment H node2826 := by
  calc
    injectiveMoment H raw3087 = injectiveMoment H raw3087step0 := by
      have heq : raw3087step0 = -raw3087 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3087).symm
    injectiveMoment H raw3087step0 = injectiveMoment H raw3087step1 := by
      have heq : raw3087step1 = (fun i j => raw3087step0 (permutation96 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3087step0 permutation96 permutation15
    _ = injectiveMoment H node2826 := by rfl

end MUB6.Certificate.PairSemantics
end OAI
