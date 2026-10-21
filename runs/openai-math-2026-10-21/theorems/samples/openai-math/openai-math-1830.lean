namespace OAI

section

namespace Erdos3

theorem positiveRetainedComplexity_exp_bounds (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    let ζ := positiveModerateRetainedBias n j t U V W ε
    let Q := positiveRetainedComplexityLog n j t p v w E
    positiveModerateSpectrumCardBudget n j t U V W ε ≤ Real.exp Q ∧
      positiveRetainedFrequencyBound n j U V ζ ≤ Real.exp Q ∧
      positiveRetainedDenominatorBound n j t U V W ζ ≤ Real.exp Q := by
  obtain ⟨_, hC, hF, hD⟩ := positiveRetainedComplexityLog_bounds n j t hp hv hw hE
  exact ⟨(positiveModerateSpectrumCardBudget_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hC),
    (positiveRetainedFrequencyBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hF),
    (positiveRetainedDenominatorBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hD)⟩

end Erdos3
end
end OAI
