@[expose] public section

open CategoryTheory

universe u

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

noncomputable section

open unitInterval

namespace Path

namespace Homotopy

section

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₀` to
  `p.trans p.symm`. -/
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm) where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by fun_prop
  map_zero_left := by simp [reflTransSymmAux]
  map_one_left x := by
    simp only [reflTransSymmAux, Path.trans]
    cases le_or_gt (x : ℝ) 2⁻¹ with
    | inl hx => simp [hx, ← extend_apply]
    | inr hx =>
      have : p.extend (2 - 2 * ↑x) = p.extend (1 - (2 * ↑x - 1)) := by ring_nf
      simpa [hx.not_ge, ← extend_apply]
  prop' t := by norm_num [reflTransSymmAux]

end
end Homotopy
end Path
end
end
