namespace OAI

namespace Laughlin.Certificate

theorem source_error_19_5_11 : Y 19 5 11 = (488068742424207599021367/2621440000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 5 11 0 (by decide),
    source_yRow_eq_rowCompute 19 5 11 1 (by decide),
    source_yRow_eq_rowCompute 19 5 11 2 (by decide),
    source_yRow_eq_rowCompute 19 5 11 3 (by decide),
    source_yRow_eq_rowCompute 19 5 11 4 (by decide),
    source_yRow_eq_rowCompute 19 5 11 5 (by decide),
    source_yRow_eq_rowCompute 19 5 11 6 (by decide),
    computeRow_19_5_11_0, computeRow_19_5_11_1, computeRow_19_5_11_2, computeRow_19_5_11_3, computeRow_19_5_11_4, computeRow_19_5_11_5, computeRow_19_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

end Laughlin.Certificate
end OAI
