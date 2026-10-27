public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

theorem commute_of_sq_mul {a c : G} (ha : a * a = 1) (hc : c * c = 1) (hca : (c * a) ^ 2 = 1) :
    a * c = c * a := by
  have h1 : c * a * (c * a) = 1 := by rw [← pow_two]; exact hca
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have h2 : c * a = (c * a)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [mul_inv_rev, hai, hci] at h2
  exact h2.symm

end CFSG.Monster.GMS
end
