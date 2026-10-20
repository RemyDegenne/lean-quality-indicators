public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

@[simp]
theorem sigPos_smul_of_pos {n : ℤ} (hn : 0 < n) (L : IntegralLattice V) :
    (n • L).sigPos = L.sigPos := by
  let _ := L.finiteDimensional
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  rw [sigPos]
  rw [smul_form, LinearMap.BilinMap.toQuadraticMap_smul]
  exact QuadraticForm.sigPos_smul_of_pos L.form.toQuadraticMap hnq

end TauCeti.IntegralLattice
end
