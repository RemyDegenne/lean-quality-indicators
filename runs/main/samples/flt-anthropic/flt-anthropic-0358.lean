namespace P2MW.S_ResidualGaloisRep_exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine

set_option autoImplicit false

set_option maxHeartbeats 6400000

noncomputable section

open scoped TensorProduct

open IsLocalRing

namespace RESID

variable {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {O : Type} [CommRing O] [IsLocalRing O] (φ : k →+* ResidueField O)
    (ρ : GaloisRepAdic O)

section A

variable (b₀ : ρ.V)

theorem baseChange_sub_smul_mem_Lbar (f : Module.End O ρ.V) (a : O)
    (hf : ∀ w : ρ.V, f w - a • w ∈ O ∙ b₀) (x : ResidueField O ⊗[O] ρ.V) :
    f.baseChange (ResidueField O) x - (algebraMap O (ResidueField O) a) • x ∈ Lbar ρ b₀ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c w =>
    rw [LinearMap.baseChange_tmul, algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      ← TensorProduct.tmul_sub]
    exact tmul_mem_Lbar_of_mem_span ρ b₀ (hf w) c
  | add x y hx hy =>
    have : f.baseChange (ResidueField O) (x + y) - (algebraMap O (ResidueField O) a) • (x + y) =
        (f.baseChange (ResidueField O) x - (algebraMap O (ResidueField O) a) • x) +
        (f.baseChange (ResidueField O) y - (algebraMap O (ResidueField O) a) • y) := by
      rw [map_add, smul_add]; abel
    rw [this]
    exact Submodule.add_mem _ hx hy

end A
end RESID
end
end P2MW.S_ResidualGaloisRep_exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine
