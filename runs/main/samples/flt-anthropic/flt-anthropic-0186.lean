namespace P2MW.S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace Metric

open scoped NNReal ENNReal Pointwise

namespace P7Rows

namespace ArchBridge

section ArchE1

theorem modulus_complex_eq_nnnorm_sq : ∀ (z : ℂ), modulus z = ‖z‖₊ ^ 2 := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [modulus_of_ne_zero hz, distribHaarChar_complex_eq_nnnorm_sq]
    simp

end ArchE1
end ArchBridge
end P7Rows
end P2MW.S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta
