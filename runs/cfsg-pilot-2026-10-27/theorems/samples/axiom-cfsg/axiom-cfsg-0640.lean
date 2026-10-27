public section

namespace CFSG.Quasithin.H13.F126

variable {W : Type*} [CommGroup W] [Finite W]

section Doubling

variable {x t : MulAut W}

variable (hW : ∀ w : W, w ^ 2 = 1) (hx3 : x ^ 3 = 1) (hxfix : ∀ w, x w = w → w = 1)
  (ht2 : t ^ 2 = 1) (htx : t * x * t⁻¹ = x ^ 2)

include hW hx3 hxfix ht2 htx in
omit [Finite W] in
theorem inf_cm : cm t ⊓ cm (t * x) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hw
  have e1 := apply_of_mem_cm hW ht2 h1
  have e2 := apply_of_mem_cm hW (tx_sq hx3 ht2 htx) h2
  rw [Subgroup.mem_bot]
  refine hxfix w ?_
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  calc x w = (t * (t * x)) w := by rw [← mul_assoc, htt, one_mul]
    _ = w := by rw [MulAut.mul_apply, e2, e1]

end Doubling
end CFSG.Quasithin.H13.F126
end
