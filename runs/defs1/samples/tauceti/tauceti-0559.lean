public section

open Module TensorProduct

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

section AbstractIntegralForm

variable {M : Type u} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- Rationalizing an integral symmetric form on a finite free `ℤ`-module produces an integral
lattice in its scalar extension to `ℚ`. -/
noncomputable def ofIntegralForm (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) :
    IntegralLattice (ℚ ⊗[ℤ] M) :=
  ofBasis ((Module.Free.chooseBasis ℤ M).baseChange ℚ) (B.baseChange ℚ)
    (LinearMap.BilinForm.isSymm_iff.mpr
      (LinearMap.BilinForm.IsSymm.baseChange ℚ (LinearMap.BilinForm.isSymm_iff.mp hB)))
    fun i j ↦ by
      rw [Basis.baseChange_apply, Basis.baseChange_apply,
        LinearMap.BilinForm.baseChange_tmul]
      simp only [one_mul, Int.smul_one_eq_cast, Submodule.mem_one]
      exact ⟨B (Module.Free.chooseBasis ℤ M i) (Module.Free.chooseBasis ℤ M j), by simp⟩

end AbstractIntegralForm
end IntegralLattice
end TauCeti
end
