public section

open Module

namespace LinearMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

theorem IsAlt.eq_zero_of_smul_apply_basis_eq_zero (b : Basis (Fin 2) R M)
    {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt) (hω : ω.SeparatingLeft) {r : R}
    (hr : r • ω (b 0) (b 1) = 0) : r = 0 := by
  have hb : r • b 0 = 0 := hω _ fun y ↦ by
    conv_lhs => rw [← b.sum_repr y]
    simp only [Fin.sum_univ_two, map_add, map_smul, smul_apply, halt (b 0), hr, smul_zero,
      add_zero]
  simpa using congr(b.repr $hb 0)

end LinearMap
end
