public section

open Module TensorProduct

open scoped Pointwise

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

variable (L : IntegralLattice V) (p : ℕ) [Fact p.Prime]

theorem localizationToCompletion_carrierDilation (n : ℤ) (hn : n ≠ 0)
    (x : L.LocalCarrier p) :
    (L.carrierDilation n hn).localizationToCompletion p
        (L.localCarrierDilationEquiv p n hn x) =
      (n : ℤ_[p]) • L.localizationToCompletion p x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul a x =>
    simp only [localCarrierDilationEquiv, LinearEquiv.baseChange_tmul,
      localizationToCompletion_tmul,
      coe_carrierDilationEquiv_apply]
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]

end TauCeti.IntegralLattice
end
