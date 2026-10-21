namespace OAI

noncomputable section

namespace Problem348.SequenceAssembly

theorem copyDensity_le_of_integer_bound {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) (A : BinaryMatrix (d * m))
    (hcount : copyCount fixedH A ≤ m * (d * m) ^ 130) :
    (copyCount fixedH A : ℝ) / (((d * m : ℕ) : ℝ) ^ 132) ≤
      (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcountR : (copyCount fixedH A : ℝ) ≤
      (m : ℝ) * ((d : ℝ) * m) ^ 130 := by exact_mod_cast hcount
  push_cast
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((d : ℝ) * m) ^ 132)).2
  calc
    (copyCount fixedH A : ℝ) ≤ (m : ℝ) * ((d : ℝ) * m) ^ 130 := hcountR
    _ = (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) * ((d : ℝ) * m) ^ 132 := by
      field_simp

end Problem348.SequenceAssembly
end
end OAI
