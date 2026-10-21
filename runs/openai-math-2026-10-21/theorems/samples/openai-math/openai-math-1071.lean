namespace OAI

universe uH uIota

open MeasureTheory Set

open scoped ENNReal symmDiff

noncomputable section

open MeasureTheory Set Filter Function Metric

open scoped Topology Convolution ContDiff

noncomputable section

open MeasureTheory Set

open scoped ENNReal

noncomputable section

open MeasureTheory Set Filter BoundedContinuousFunction

open scoped ENNReal Topology ComplexConjugate

noncomputable section

open MeasureTheory Set Filter

open scoped Topology ComplexConjugate

noncomputable section

open MeasureTheory Filter

open scoped ComplexConjugate

noncomputable section

open MeasureTheory Filter Set

open scoped Topology ComplexConjugate

noncomputable section

open Filter Finset Set

open scoped Topology BigOperators

noncomputable section

open MeasureTheory Filter Set

open scoped Topology ContDiff NNReal

open MeasureTheory Filter Set

open scoped Topology ComplexConjugate

noncomputable section

open Filter Set

open scoped Topology

noncomputable section

namespace TriangularBilliards.Analysis

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {T : ℝ} [Fact (0 < T)]

omit [CompleteSpace H] in
lemma CR_components_eq {a b c d : H} (hx : a+b=c+d)
    (hy : Complex.I • (a-b) = Complex.I • (c-d)) : a=c ∧ b=d := by
  have hd : a-b=c-d := smul_right_injective H Complex.I_ne_zero hy
  have haa : (2 : ℂ) • a = (2 : ℂ) • c := by
    calc
      _ = (a+b)+(a-b) := by module
      _ = (c+d)+(c-d) := by rw [hx,hd]
      _ = _ := by module
  have ha := smul_right_injective H (by norm_num : (2 : ℂ) ≠ 0) haa
  exact ⟨ha, add_left_cancel (ha ▸ hx)⟩

end TriangularBilliards.Analysis
end
end
end
end
end
end
end
end
end
end
end OAI
