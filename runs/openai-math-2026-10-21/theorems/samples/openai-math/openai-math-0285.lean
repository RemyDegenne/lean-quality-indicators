namespace OAI

namespace HarmonicArtin.ParabolicIntersections.GraphRealization

variable {V : Type} (H : SimpleGraph V) (hH : H.Connected)

lemma curve_to_anchor (p : Point H) (i : Bool) :
    HasCurve (embed H hH p) (vertex H hH (anchor H p i)) (weight H p i) := by
  cases p with
  | vertex v => exact curve_const _
  | edge e t =>
    cases i
    · have h := arc_curve H hH e t ⟨0,by norm_num⟩
      change HasCurve (arc H hH e t) (vertex H hH e.fst) (t : ℝ)
      simpa only [arc_zero,sub_zero,abs_of_nonneg t.property.1] using h
    · have h := arc_curve H hH e t ⟨1,by norm_num⟩
      change HasCurve (arc H hH e t) (vertex H hH e.snd) (1-(t : ℝ))
      simpa only [arc_one,abs_of_nonpos (sub_nonpos.mpr t.property.2),neg_sub] using h

end HarmonicArtin.ParabolicIntersections.GraphRealization
end OAI
