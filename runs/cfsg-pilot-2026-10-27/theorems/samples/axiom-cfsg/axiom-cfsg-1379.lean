public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

open scoped MatrixGroups commutatorElement

section Element

variable {τ : Tag} {K : Type} [Field K]

theorem pinnedX_sign_not_mem_rootSubgroup_sup {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hne : δ ≠ γ) (hne' : δ ≠ -γ) {c : K} (hc : c = 1 ∨ c = -1) :
    pinnedX τ K δ c ∉ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
  let ℓ : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun v => iform γ γ * iform v δ - iform δ γ * iform v γ
      map_zero' := by
        have h1 := iform_smul_left (τ := τ) 0 0 δ
        have h2 := iform_smul_left (τ := τ) 0 0 γ
        simp only [smul_zero, zero_mul] at h1 h2
        rw [h1, h2]
        ring
      map_add' := fun u v => by
        rw [iform_add_left, iform_add_left]
        ring }
  have hℓγ : ℓ γ = 0 := by
    change iform γ γ * iform γ δ - iform δ γ * iform γ γ = 0
    rw [iform_comm δ γ]
    ring
  have hℓδ : ℓ δ ≠ 0 := by
    change iform γ γ * iform δ δ - iform δ γ * iform δ γ ≠ 0
    have h := iform_sq_lt hδ hγ hne hne'
    nlinarith
  intro hmem
  have hX : pinnedX τ K δ 1 ∈ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
    rcases hc with rfl | rfl
    · exact hmem
    · rw [← inv_mem_iff, pinnedX_neg] at hmem
      simpa using hmem
  exact pinnedX_one_not_mem_gradingSubgroup ℓ hδ hℓδ
    (rootSubgroup_sup_le_gradingSubgroup ℓ hγ hℓγ hX)

end Element
end CFSG.ClassicalInvolution.ModelFacts
end
