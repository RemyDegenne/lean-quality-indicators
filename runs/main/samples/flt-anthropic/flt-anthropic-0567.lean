namespace P2MW.S_HeckeEis_exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd

set_option autoImplicit false

namespace CupThree

open CongruenceSubgroup HeckeEis

open scoped MatrixGroups

section Coinduced

variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type*) [CommRing κ]

@[scoped simp] theorem rhoX_apply (g : SL(2, ℤ)) (U : ZMod 3 → Q M → κ) (i : ZMod 3) (y : Q M) :
    rhoX M h3M κ g U i y = U (i + cc M g y) (g⁻¹ • y) := rfl

end Coinduced
end CupThree
end P2MW.S_HeckeEis_exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd
