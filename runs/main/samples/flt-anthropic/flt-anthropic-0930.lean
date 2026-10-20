namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {L : Type} [Field L] [CharZero L]

section Good

variable (hmM' : Nat.Coprime m M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ξ : L)
  (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq m)

variable {hmM' γ hγ ι₀}

include hι₀ in

theorem Good.of_mem_field {x : LaurentSeries ℚ} (hx : x ∈ xHFunctionField (m ^ 2 * M') (levelH m M')) :
    Good hmM' γ hγ ι₀ (coeffEmb L x) := by
  change x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH m M')) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact good_algebraMap _
      · exact Good.gen ξ hι₀ hy
  | one => rw [map_one]; exact Good.one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

end Good
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
