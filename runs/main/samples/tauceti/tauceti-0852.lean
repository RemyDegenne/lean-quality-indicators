public section

open scoped DirectSum

universe u v

namespace CliffordAlgebra

open TauCeti.Algebra.wordFiltration

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

theorem exteriorPower_succ_disjoint_zero_form_filtration (k : ℕ) :
    Disjoint (⋀[R]^(k + 1) M) (filtration (0 : QuadraticForm R M) k) := by
  rw [filtration_eq_iSup_pow (0 : QuadraticForm R M) k]
  rw [iSup_subtype]
  have hind : iSupIndep (fun i : ℕ => ⋀[R]^i M) :=
    (DirectSum.Decomposition.isInternal (fun i : ℕ => ⋀[R]^i M)).submodule_iSupIndep
  simpa only [Set.mem_Iic] using hind.disjoint_biSup (by simp : k + 1 ∉ Set.Iic k)

end CliffordAlgebra
end
