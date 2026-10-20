public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F K L : Type*} [Field F] [Field K] [Field L]
  {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

@[simp]
theorem degree_map (h : Hom W₁ W₂) (f : F →+* K) : (h.map f).degree = h.degree := by
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩ <;> simp

end TauCeti.Isogeny.Hom
end
