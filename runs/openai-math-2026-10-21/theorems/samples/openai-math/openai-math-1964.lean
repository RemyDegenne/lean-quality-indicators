namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF

theorem dualAdjoint_realBasis_coordinate (g : F.realification.Group) (i k : ι)
    (hki : ω k ≤ ω i) :
    (b.baseChange ℝ).repr (dualAdjoint g ((b.baseChange ℝ) i)) k =
      (b.baseChange ℝ).repr ((b.baseChange ℝ) i) k := by
  have hd := F.realification.dualAdjoint_sub_mem_next_layer (ω i) g ((b.baseChange ℝ) i)
    (F.realBasis_mem_layer b ω hF i)
  have hz := (F.real_mem_layer_iff_basis_coordinates b ω hF (ω i + 1) _).mp hd k
    (by omega)
  simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using hz

end Erdos3.NilpotentLieFiltration
end
end OAI
