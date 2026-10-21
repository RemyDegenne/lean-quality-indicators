namespace OAI

noncomputable section

open Set

open scoped ENNReal

open Set Filter Topology

open scoped Classical

namespace BoundedTreePotentials.Segments

lemma polar_pairing_bound (z g : Node →₀ ℝ) :
    |finitePairing g z| ≤ testNorm unitTests z*testNorm atomTests g := by
  let R := testNorm atomTests g
  have hR := testNorm_nonneg atomTests g
  by_cases hz : R=0
  · have hg : g=0 := (testNorm_eq_zero atomTests g).mp hz
    subst g
    simp [finitePairing, testNorm_zero]
  · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
    have hu : IsUnitTest (R⁻¹ • (g : Node → ℝ)) := by
      have hh : testNorm atomTests (R⁻¹ • g) ≤ 1 := by
        calc
          _ ≤ ‖R⁻¹‖*testNorm atomTests g := testNorm_smul_le atomTests _ _
          _ = 1 := by rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]; exact inv_mul_cancel₀ hz
      exact (predual_unit_iff (R⁻¹ • g)).mp hh
    have hh := finitePairing_le_testNorm unitTests ⟨_,hu⟩ z
    rw [finitePairing_coeff_smul,abs_mul,abs_of_pos (inv_pos.mpr hp)] at hh
    have he := mul_le_mul_of_nonneg_left hh hp.le
    rw [← mul_assoc,mul_inv_cancel₀ hz,one_mul] at he
    simpa only [R,mul_comm] using he

end BoundedTreePotentials.Segments
end
end OAI
