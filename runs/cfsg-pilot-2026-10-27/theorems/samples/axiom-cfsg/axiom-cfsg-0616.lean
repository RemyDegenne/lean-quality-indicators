public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec.Z6NA

theorem cvec_vcode_vec6 : ∀ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2,
    cvec (vcode (vec6 x₀ x₁ x₂ x₃ x₄ x₅)) = vec6 x₀ x₁ x₂ x₃ x₄ x₅ := by
  decide

end CFSG.CGT.Foote82.OmegaSix
end
