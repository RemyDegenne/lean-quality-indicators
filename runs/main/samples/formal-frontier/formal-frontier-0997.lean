set_option warningAsError true

@[expose] public section

namespace TwoSidedIdeal

universe u

variable {R : Type u} [Ring R]

theorem exists_quasiInverse_mem_of_isRightQuasiregular
    {I : TwoSidedIdeal R} (h : I.IsRightQuasiregular)
    {x : R} (hxI : x ∈ I) :
    ∃ y : R, y ∈ I ∧
      x + y + x * y = 0 ∧ x + y + y * x = 0 := by
  obtain ⟨y, hyI, hxy⟩ := h x hxI
  have hab : (1 + x) * (1 + y) = 1 := by
    calc
      (1 + x) * (1 + y) = 1 + (x + y + x * y) := by noncomm_ring
      _ = 1 := by rw [hxy, add_zero]
  let z : R := y + x + y * x
  have hzI : z ∈ I :=
    I.add_mem (I.add_mem hyI hxI) (I.mul_mem_right y x hyI)
  obtain ⟨w, _hwI, hzw⟩ := h z hzI
  have hbaRight : ((1 + y) * (1 + x)) * (1 + w) = 1 := by
    calc
      ((1 + y) * (1 + x)) * (1 + w) =
          (1 + z) * (1 + w) := by
            congr 1
            simp only [z]
            noncomm_ring
      _ = 1 + (z + w + z * w) := by noncomm_ring
      _ = 1 := by rw [hzw, add_zero]
  have hidem :
      ((1 + y) * (1 + x)) * ((1 + y) * (1 + x)) =
        (1 + y) * (1 + x) := by
    calc
      ((1 + y) * (1 + x)) * ((1 + y) * (1 + x)) =
          (1 + y) * ((1 + x) * (1 + y)) * (1 + x) := by
            simp only [mul_assoc]
      _ = (1 + y) * (1 + x) := by rw [hab]; simp
  have hba : (1 + y) * (1 + x) = 1 := by
    calc
      (1 + y) * (1 + x) = ((1 + y) * (1 + x)) * 1 := by rw [mul_one]
      _ = ((1 + y) * (1 + x)) *
          (((1 + y) * (1 + x)) * (1 + w)) := by rw [hbaRight]
      _ = (((1 + y) * (1 + x)) * ((1 + y) * (1 + x))) *
          (1 + w) :=
        (mul_assoc ((1 + y) * (1 + x)) ((1 + y) * (1 + x)) (1 + w)).symm
      _ = ((1 + y) * (1 + x)) * (1 + w) := by rw [hidem]
      _ = 1 := hbaRight
  refine ⟨y, hyI, hxy, ?_⟩
  have hyx : (1 + y) * (1 + x) = 1 + (x + y + y * x) := by
    noncomm_ring
  rw [hyx] at hba
  exact add_left_cancel (hba.trans (add_zero 1).symm)

end TwoSidedIdeal
end
