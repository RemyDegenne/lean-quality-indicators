namespace OAI

noncomputable section

namespace InternalCatalan.ManuscriptPrecision

theorem all_XP_point_log_input_ranges {x : ℚ} (hx : x ∈ Case2PointData.XPoints)
    {zr : ℂ × ℂ} (hzr : zr ∈ barrierP2Tail) :
    ComplexLogInputRange (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2) := by
  have hx' : x ∈ paperXPoints := List.mem_append.mpr (Or.inl hx)
  simpa only [Complex.ofReal_ratCast] using
    actual_XP_log_argument_range (paper_X_point_margins x hx').1 hzr

end InternalCatalan.ManuscriptPrecision
end
end OAI
