public section

namespace TauCeti.Isogeny

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

namespace Hom

@[simp]
theorem degree_comp (g : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (g.comp f).degree = g.degree * f.degree := by
  rcases g.eq_zero_or_exists_ofIsogeny with rfl | ⟨ψ, rfl⟩
  · rw [zero_comp, degree_zero, degree_zero, zero_mul]
  · rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
    · rw [comp_zero, degree_zero, degree_zero, mul_zero]
    · rw [ofIsogeny_comp_ofIsogeny, degree_ofIsogeny, degree_ofIsogeny, degree_ofIsogeny,
        Isogeny.degree_comp]

end Hom
end TauCeti.Isogeny
end
