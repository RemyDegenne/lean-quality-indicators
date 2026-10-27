public section

open MeasureTheory

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The logarithmic time weight at time 3/2 in the manuscript. -/
@[expose] def buGaussianH : ℝ := Real.log (gaussCarlemanTimeWeight (3 / 2))

end ESS
end
end
