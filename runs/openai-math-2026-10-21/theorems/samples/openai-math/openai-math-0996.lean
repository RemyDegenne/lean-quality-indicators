namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

section

open _root_.Filter

open scoped Topology

namespace ErdosInverseCells

open ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin

open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints NumberTheoryLean.LogarithmicBinPartition

theorem actual_cofactor_effective_range {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ) (q : ℕ)
    (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    cofactorScale z xi m/(1+effectiveWidth (sourceW z) z xi)^(∑ i,m i) ≤ (q : ℝ) ∧
      (q : ℝ) ≤ cofactorScale z xi m := by
  have hupper := (actual_cofactor_range hw hwz hxi m q hq).2
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
  have htheta := effectiveWidth_pos hw hwz hxi
  have hF : 0 < 1+effectiveWidth (sourceW z) z xi := by linarith
  have hU : ∀ i : Fin (binCount (sourceW z) z xi),0 ≤ upper (sourceW z) z xi i := by
    intro i
    have hb := bin_source_bounds hw hwz hxi i
    exact ((hw.trans_le hb.1).trans hb.2.1).le
  have hlower : ∀ i : Fin (binCount (sourceW z) z xi),∀ p ∈ actualBins z xi i,
      upper (sourceW z) z xi i/(1+effectiveWidth (sourceW z) z xi) ≤ (p : ℝ) := by
    intro i p hp
    have hh := (mem_primeBin (endpoint_pos hw i.1).le htheta.le p).mp hp
    have he : upper (sourceW z) z xi i/(1+effectiveWidth (sourceW z) z xi) = lower (sourceW z) z xi i := by
      change ((1+effectiveWidth (sourceW z) z xi)*lower (sourceW z) z xi i)/(1+effectiveWidth (sourceW z) z xi) = _
      field_simp
    rw [he]
    exact hh.2.1.le
  exact ⟨selectionProduct_lower (actualBins z xi) m f hf (upper (sourceW z) z xi) hU
    (1+effectiveWidth (sourceW z) z xi) hF hlower,hupper⟩

end ErdosInverseCells
end
end Erdos970
end OAI
