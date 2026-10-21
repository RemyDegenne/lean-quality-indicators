namespace OAI

section

section

namespace DilutedSpinGlass

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set

lemma boundParameter_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    boundParameter a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

end DilutedSpinGlass
end
end
end OAI
