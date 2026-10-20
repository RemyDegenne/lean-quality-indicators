public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

theorem modFormCharSpace_eq_bot_of_char_neg_one_ne (h : (χ (-1) : ℂ) ≠ (-1 : ℂ) ^ k) :
    modFormCharSpace (N := N) k χ = ⊥ :=
  Submodule.eq_bot_iff _ |>.mpr fun _f hf ↦
    not_not.mp fun hf0 ↦ h (char_neg_one_of_mem_modFormCharSpace hf hf0)

end TauCeti
end
