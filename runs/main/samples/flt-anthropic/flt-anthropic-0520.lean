set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech

section Carrier

variable (R : Type u) [CommRing R] (n : ℕ)

attribute [instance] GradedModule.acg GradedModule.modR

variable {R n}

variable (D : GradedModule R n)

theorem GradedModule.xMul_pow_mem_grade (j : Fin (n + 1)) (k : ℕ) (d : ℤ) :
    ∀ m ∈ D.grade d, (D.xMul j ^ k) m ∈ D.grade (d + k) := by
  induction k with
  | zero => intro m hm; simpa using hm
  | succ k' ihk =>
    intro m hm
    have h1 := D.xMul_mem_grade j (d + k') _ (ihk m hm)
    have h2 : (D.xMul j ^ (k' + 1)) m = D.xMul j ((D.xMul j ^ k') m) := by
      rw [pow_succ']; rfl
    rw [h2]; convert h1 using 2; push_cast; ring

end Carrier
end ProjSpaceCech
end
