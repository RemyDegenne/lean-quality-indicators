open CFSG

noncomputable section

open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe v

universe u

theorem theorem_6_7_affine_solve_rat
    (C r m n : ℕ) (x : ℂ)
    (hC : (C : ℂ) ≠ 0) (hr : (r : ℂ) ≠ 0)
    (h : (C : ℂ)⁻¹ * ((n : ℂ) + (r : ℂ) * x) = (m : ℂ)) :
    ∃ q : ℚ, x = (q : ℂ) := by
  refine ⟨((C : ℚ) * (m : ℚ) - (n : ℚ)) / (r : ℚ), ?_⟩
  have h' : (n : ℂ) + (r : ℂ) * x = (C : ℂ) * (m : ℂ) := by
    calc
      (n : ℂ) + (r : ℂ) * x =
          (C : ℂ) * ((C : ℂ)⁻¹ * ((n : ℂ) + (r : ℂ) * x)) := by
        field_simp [hC]
      _ = (C : ℂ) * (m : ℂ) := by rw [h]
  have h'' : (r : ℂ) * x = (C : ℂ) * (m : ℂ) - (n : ℂ) := by
    rw [← h']
    ring
  calc
    x = ((C : ℂ) * (m : ℂ) - (n : ℂ)) / (r : ℂ) := by
      field_simp [hr]
      rw [mul_comm x (r : ℂ), h'']
    _ = ((((C : ℚ) * (m : ℚ) - (n : ℚ)) / (r : ℚ) : ℚ) : ℂ) := by
      norm_num

end CFSG.Section6
end
