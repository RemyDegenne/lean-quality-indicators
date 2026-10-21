namespace OAI

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric

open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace GeneralMahler

open Layers

variable {m:ℕ}

variable [NeZero m]

namespace Edge

variable (e:Edge m)

lemma Jedge_bound (x) : scalar m (MillsC (e.radius x)) ≤ e.Jedge x := by
  let a := e.radius x
  have hf := integral_add_compl measurableSet_Iic (e.wp_slice_i x) (s:=Iic a)
  rw [compl_Iic] at hf
  have hh : (∫ z in Ioi a,e.WP z x) = scalar m (MillsC a) := by
    rw [← (mw_tail a).2,scalar,← integral_smul_const]
    exact setIntegral_congr_fun measurableSet_Ioi fun z hz=>by rw [WP,e.tend_pos _ _ hz]
  have hi : (0:Mat m) ≤ ∫ z in Iic a,e.WP z x :=
    (psd_integral (e.wp_slice_i x).integrableOn (ae_of_all _ fun z=>(e.wp_psd z x).posSemidef)).nonneg
  unfold Jedge
  rw [← hf,hh]; exact le_add_of_nonneg_left hi

end Edge
end GeneralMahler
end
end OAI
