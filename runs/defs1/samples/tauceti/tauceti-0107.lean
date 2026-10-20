public section

namespace TauCeti

open scoped Matrix

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

variable {k : Type*} [CommRing k]

variable {v : ConjClasses G → k}

/-- **The algebra homomorphism attached to a normalized common left eigenrow**: the linear extension
of `v` along the class-sum basis. Multiplicativity is the eigenrow condition read through the
coordinate identity, and it is unital because the class sum at the class of `1` is `1`. -/
noncomputable def eigenrowAlgHom (hv₁ : v (ConjClasses.mk (1 : G)) = 1)
    (hv : IsClassEigenrow v) : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
  AlgHom.ofLinearMap (Module.Basis.constr classSumBasis k v)
    (by
      rw [← classSumCenter_mk_one, ← classSumBasis_apply, Module.Basis.constr_basis]
      exact hv₁)
    (map_mul_of_basis fun Cᵢ Cⱼ => by
      rw [classSumCenter_mul]
      simp only [map_sum, map_smul, smul_eq_mul, ← classSumBasis_apply,
        Module.Basis.constr_basis]
      exact (isClassEigenrow_iff v).mp hv Cᵢ Cⱼ)

end TauCeti
end
