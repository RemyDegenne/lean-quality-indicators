@[expose] public section

namespace NRR

variable {n : ℕ}

namespace EMP

/-- **Weight mean.** The arithmetic mean `(∑ i, w i) / n` of a weight vector. -/
noncomputable def weightMean (w : Fin n → ℝ) : ℝ :=
  EMP.weightSum w / n

end EMP
end NRR
end
