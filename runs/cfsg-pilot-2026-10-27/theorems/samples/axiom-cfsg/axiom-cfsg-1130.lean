public section

namespace CFSG.LargeEvenClassification.Helpers

theorem top_scalar_fixed_long_coordinate (exponent : ℕ)
    (x : ZMod (2 ^ (exponent + 3)))
    (hfixed : (1 + (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2)) * x = x) :
    ∃ y : ZMod (2 ^ (exponent + 3)), x = 2 • y := by
  obtain ⟨y, hy⟩ := binaryCongruenceInvolution_fixed_square exponent x
    (by rw [binaryCongruenceInvolution_val]; exact hfixed)
  refine ⟨y, ?_⟩
  simpa only [two_nsmul] using hy.symm

end CFSG.LargeEvenClassification.Helpers
end
