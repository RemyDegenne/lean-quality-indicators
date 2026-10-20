namespace P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open PDivisibleGroup Filter Topology

open scoped TensorProduct

namespace PDivStep2R

variable (p : ℕ) [Fact p.Prime]

section TatePlumbing

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]

def tmap (φ : M →+ N) : TateModule p M →ₗ[ℤ_[p]] TateModule p N where
  toFun x := ⟨fun n => φ ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero], by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    change φ (((x + y : TateModule p M) : ℕ → M) n) = φ ((x : ℕ → M) n) + φ ((y : ℕ → M) n)
    rw [AddSubgroup.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    change φ (((a • x : TateModule p M) : ℕ → M) n) = ((a • _ : TateModule p N) : ℕ → N) n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

end TatePlumbing
end PDivStep2R
end
end P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
