namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_single_slope_characters {R : Type*} [CommRing R]
    (a : R) (Psi : AddChar (R × R) ℂ) :
    ∃ chi rho : AddChar R ℂ, ∀ u d, Psi (u - a * d, d) = chi u * rho d := by
  let L : R →+ (R × R) := { toFun := fun u => (u, 0), map_zero' := rfl, map_add' := by intros; simp }
  let M : R →+ (R × R) := {
    toFun := fun d => (-a * d, d)
    map_zero' := by simp
    map_add' := by intro x y; ext <;> simp [mul_add] }
  refine ⟨Psi.compAddMonoidHom L, Psi.compAddMonoidHom M, ?_⟩
  intro u d
  change Psi (u - a * d, d) = Psi (u, 0) * Psi (-a * d, d)
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ext <;> simp [sub_eq_add_neg]

end Erdos3
end
end OAI
