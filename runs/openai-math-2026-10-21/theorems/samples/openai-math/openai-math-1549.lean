namespace OAI

noncomputable section

open Set MeasureTheory

open scoped CompactlySupported

namespace CubicFirstMoment

lemma cubicThetaGramDenominatorIntegral_eq (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {c : Eisenstein} (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (ε : ℝ) :
    cubicThetaGramDenominatorIntegral h k W V c ε=
      cubicThetaKloostermanSum h k c hc*cubicThetaArchimedeanGram h k W V (c:ℂ) ε := by
  unfold cubicThetaGramDenominatorIntegral cubicThetaArchimedeanGram
  simp only [cubicThetaGramKloostermanTerm,dite_eq_left (And.intro hc hc0)]
  simp_rw [show ∀ v : ℝ,star (W v)/(v:ℂ)^3*
      (cubicThetaKloostermanSum h k c hc*∫ z,cubicThetaGramInversionKernel h k V (c:ℂ) z v)=
        cubicThetaKloostermanSum h k c hc*
          (star (W v)/(v:ℂ)^3*∫ z,cubicThetaGramInversionKernel h k V (c:ℂ) z v) by
    intro v; ring]
  exact integral_const_mul _ _

end CubicFirstMoment
end
end OAI
