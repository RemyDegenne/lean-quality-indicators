namespace OAI

namespace Falconer

attribute [local instance] Classical.propDecidable

theorem localCellLine_chart {Δ y a : ℝ} (hΔ : 0 < Δ) (hΔsmall : Δ ≤ 1/8)
    (p l : Space 2) (hp0 : |p 0-y| ≤ Δ/4) (hp1 : |p 1-a| ≤ Δ/4)
    (hl0 : |l 0| ≤ 1/2) (hi : TubeIncident (Δ^2) p l) :
    |localCellLine Δ y a l 0| ≤ 1 ∧ |localCellLine Δ y a l 1| ≤ 1 := by
  have hres := tube_residual_le (sq_nonneg Δ) (hl0.trans (by norm_num)) hi
  have hb : |l 0*y+l 1-a| ≤ Δ/4+Δ/8+2*Δ^2 := by
    calc
      _ = |(p 1-a)-l 0*(p 0-y)-(p 1-l 0*p 0-l 1)| := by congr 1; ring
      _ ≤ |(p 1-a)-l 0*(p 0-y)|+|p 1-l 0*p 0-l 1| := abs_sub _ _
      _ ≤ (|p 1-a|+|l 0*(p 0-y)|)+|p 1-l 0*p 0-l 1| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ Δ/4+(1/2)*(Δ/4)+2*Δ^2 := by rw [abs_mul]; gcongr
      _ = _ := by ring
  refine ⟨hl0.trans (by norm_num),?_⟩
  change |(l 0*y+l 1-a)/Δ| ≤ 1
  rw [abs_div,abs_of_pos hΔ,div_le_one hΔ]
  exact hb.trans (by nlinarith only [hΔsmall,mul_nonneg hΔ.le (sub_nonneg.mpr hΔsmall)])

end Falconer
end OAI
