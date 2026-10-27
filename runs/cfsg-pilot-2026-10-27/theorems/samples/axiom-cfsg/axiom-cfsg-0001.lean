public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice

theorem signVec_pairVec_comp (a : Fin 24 → ZMod 2) (p : Equiv.Perm (Fin 24)) (x y : Fin 24)
    (b : ZMod 2) :
    signVec a (pairVec x y b) ∘ ⇑p⁻¹ = sgnI (a x) • pairVec (p x) (p y) (b + a x + a y) := by
  funext m
  have h1 : ∀ z : Fin 24, (p⁻¹ m = z) ↔ (m = p z) := fun z => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [Function.comp_apply, signVec_apply', Pi.smul_apply, smul_eq_mul, pairVec_apply,
    h1, sgnI_add]
  have hx2 := sgnI_mul_self (a x)
  by_cases hmx : m = p x
  · have hpx : p⁻¹ m = x := (h1 x).2 hmx
    rw [hpx]
    by_cases hmy : m = p y
    · have hxy : x = y := p.injective (hmx.symm.trans hmy)
      subst hxy
      simp only [ite_eq_left hmx]
      linear_combination (4 * sgnI b * sgnI (a x)) * hx2
    · simp only [ite_eq_left hmx, ite_eq_right hmy]
      ring
  · by_cases hmy : m = p y
    · have hpy : p⁻¹ m = y := (h1 y).2 hmy
      rw [hpy]
      simp only [ite_eq_right hmx, ite_eq_left hmy]
      linear_combination (4 * sgnI b * sgnI (a y)) * hx2
    · simp only [ite_eq_right hmx, ite_eq_right hmy]
      ring

end CFSG.Monster.B.TwoA
end
