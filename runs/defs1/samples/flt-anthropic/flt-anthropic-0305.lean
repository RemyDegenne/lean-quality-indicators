namespace P2MW.S_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

open scoped NumberField

namespace AnnulusUnif

noncomputable scoped instance instNumberFieldIntermediateField (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField ↥K :=
  { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

section Transport

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (red : A →+* k)
  (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) [FiniteDimensional ℚ K]

noncomputable def ψ (hq𝔭 : ((q : ℕ) : 𝓞 ↥K) ∈ 𝔭 A K) (hqV : ¬ IsUnit ((q : ℕ) : ↥(V A K))) :
    ↥(D A K) ≃+* ↥(coeffSubring A K) where
  toFun y := ⟨((y : ↥K) : AlgebraicClosure ℚ), ⟨(mem_V A K).mp (mem_V_of_mem_D A K _ y.2), (y : ↥K).2⟩⟩
  invFun d := ⟨⟨(d : AlgebraicClosure ℚ), d.2.2⟩,
    mem_D_of_mem_V A K hq𝔭 hqV _ ((mem_V A K).mpr (by exact d.2.1))⟩
  left_inv y := rfl
  right_inv d := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end Transport
end AnnulusUnif
end P2MW.S_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
