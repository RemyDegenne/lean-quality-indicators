namespace OAI

universe uE uX uι uα

noncomputable section

namespace PettyProjection.FixedPoint

open scoped RealInnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_add_smul_sq (c v : E) (t : ℝ) :
    ‖c+t • v‖^2=‖c‖^2+2*t*⟪c,v⟫+t^2*‖v‖^2 := by
  simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,conj_trivial]
  rw [real_inner_comm v c]
  ring

end PettyProjection.FixedPoint
end
end OAI
