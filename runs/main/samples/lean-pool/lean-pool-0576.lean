section

section

@[expose] public section

noncomputable section

namespace EulerFiniteGrades

open Finset

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

theorem convolution_strict_congr (M p : ℕ) (hp : 0 < p) (hMp : p ≤ M)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u u' : ℕ → V) (hu0 : u 0 = 0)
    (hu : ∀ i < p, u' i = u i) :
    convolution M B u' u' p = convolution M B u u p := by
  rw [convolution_eq_range M p hMp, convolution_eq_range M p hMp]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ p := by have h := mem_range.mp hi; omega
  by_cases hi0 : i=0
  · simp only [hi0, hu 0 hp, hu0, map_zero, LinearMap.zero_apply]
  by_cases hip : i=p
  · simp only [hip, Nat.sub_self, hu 0 hp, hu0, map_zero]
  rw [hu i (by omega), hu (p-i) (by omega)]

end EulerFiniteGrades
end
end
end
end
