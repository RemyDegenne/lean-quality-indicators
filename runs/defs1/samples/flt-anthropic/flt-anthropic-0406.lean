namespace P2MW.S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient

set_option autoImplicit false

noncomputable section

p2m_open

open scoped Topology Manifold MatrixGroups ModularForm

namespace WLight

p2m_open

section GlueBFold

open ModularForm

namespace R8cGlue

section Kit

variable {N : ℕ}

variable (jf : ℍ → ℂ) (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)

variable {jf fricke}

def genPerm (γ : SL(2, ℤ)) :
    Option {v : Fin 2 → ZMod N // v ≠ 0} → Option {v : Fin 2 → ZMod N // v ≠ 0} :=
  Option.map fun v => ⟨Matrix.vecMul v.1
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)), by
    intro h
    apply v.2
    have := congrArg (fun w => Matrix.vecMul w
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ⁻¹ :
        Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) h
    simp only [Matrix.zero_vecMul, Matrix.vecMul_vecMul] at this
    rwa [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one] at this⟩

end Kit
end R8cGlue
end GlueBFold
end WLight
end
end P2MW.S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient
