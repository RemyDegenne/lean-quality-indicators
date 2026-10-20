public section

open ValuativeRel IsLocalRing Submodule MulAction

open scoped Pointwise

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- **The span of the orbit is free of rank one over the group ring.** If the conjugates of
`α ∈ 𝒪[L]` are linearly independent over `K`, then `∑ σ, r_σ σ ↦ ∑ σ, r_σ • σ α` is an
isomorphism from the group ring `𝒪[K][G]`, with `G` acting by left multiplication, onto the
`𝒪[K]`-span of the orbit of `α`, with the Galois action restricted from `𝒪[L]`. -/
noncomputable def spanOrbitEquiv {α : 𝒪[L]}
    (h : LinearIndependent K fun σ : L ≃ₐ[K] L ↦ σ (α : L)) :
    (Representation.leftRegular 𝒪[K] (L ≃ₐ[K] L)).Equiv
      ((Representation.ofDistribMulAction 𝒪[K] (L ≃ₐ[K] L) 𝒪[L]).subrepresentation
        (span 𝒪[K] (orbit (L ≃ₐ[K] L) α))
        fun σ ↦ (Module.End.mem_invtSubmodule _).1 <|
          Module.End.span_orbit_mem_invtSubmodule _ α σ) :=
  .mk ((MonoidAlgebra.coeffLinearEquiv 𝒪[K]).trans
    ((linearIndependent_smul_integerRing h).linearCombinationEquiv.trans
      (.ofEq _ _ (by rw [orbit])))) fun τ ↦ by
    ext σ : 2
    refine Subtype.ext ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply,
      Representation.ofMulAction_single, smul_eq_mul, LinearEquiv.coe_coe,
      Representation.subrepresentation_apply, LinearMap.coe_restrict_apply,
      Representation.ofDistribMulAction_apply_apply]
    rw [coe_linearCombinationEquiv_coeffLinearEquiv_single h,
      coe_linearCombinationEquiv_coeffLinearEquiv_single h]
    simp [mul_smul]

end TauCeti
end
