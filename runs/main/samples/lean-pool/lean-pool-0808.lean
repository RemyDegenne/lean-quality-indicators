@[expose] public section

noncomputable section

notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

section

@[expose] public section

namespace LeanCert.Core

namespace IntervalRat

theorem mem_evalTaylorSeries_atanh {q : ℚ} (n : ℕ) :
    ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum ∈
      evalTaylorSeries (atanhTaylorCoeffs n) (singleton q) :=
  mem_evalTaylorSeries (mem_singleton q) (atanhTaylorCoeffs n)

end IntervalRat
end LeanCert.Core
end
end
end
end
