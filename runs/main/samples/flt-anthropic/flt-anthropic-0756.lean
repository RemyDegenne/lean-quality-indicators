namespace P2MW.S_ProjSpaceCech_Twist_finite_cohomology

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function

namespace ProjSpaceCech

p2m_open

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

section Homotopy

variable {n : ℕ}

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

variable (R : Type u) [CommRing R] (d : ℤ)

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.coeff_of_not {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n)
    (h : ¬ Twist.negSupp n a ⊆ Idx.img n s) :
    Twist.coeff R d f s a = 0 := by
  rw [Twist.coeff, dif_neg (fun h' => h h'.2)]

end Homotopy
end Cohomology
end ProjSpaceCech
end
end P2MW.S_ProjSpaceCech_Twist_finite_cohomology
