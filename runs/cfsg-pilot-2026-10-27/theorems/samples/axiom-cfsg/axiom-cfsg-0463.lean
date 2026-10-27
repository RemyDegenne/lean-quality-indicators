public section

noncomputable section

open CFSG.Quasithin CFSG.ASVolI.ChH

open CFSG.Quasithin.H13.H11P

open CFSG.RankThree.PartOne.KCRootAxis

open scoped Matrix

namespace CFSG.LocalAnalysis.WeakClosure81

local notation "F₄" => GaloisField 2 2

local notation "M₄" => Matrix (Fin 2) (Fin 2) F₄

lemma exists_smul_or_smul_of_finrank_range_eq_one
    {u : M₄ →ₗ[F₄] M₄} (hu : Module.finrank F₄ (LinearMap.range u) = 1)
    {V W : M₄} (hV : V ∈ LinearMap.range u) (hW : W ∈ LinearMap.range u) :
    (∃ γ : F₄, W = γ • V) ∨ (∃ γ : F₄, V = γ • W) := by
  obtain ⟨z, hz0, hgen⟩ :=
    (finrank_eq_one_iff' (K := F₄) (V := LinearMap.range u)).mp hu
  obtain ⟨c, hc⟩ := hgen ⟨V, hV⟩
  obtain ⟨d, hd⟩ := hgen ⟨W, hW⟩
  have hVz : V = c • (z : M₄) := by
    have := congrArg Subtype.val hc
    simpa using this.symm
  have hWz : W = d • (z : M₄) := by
    have := congrArg Subtype.val hd
    simpa using this.symm
  by_cases hc0 : c = 0
  · right
    refine ⟨0, ?_⟩
    simp [hVz, hc0]
  · left
    have hz : (z : M₄) = c⁻¹ • V := by
      rw [hVz, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    refine ⟨d * c⁻¹, ?_⟩
    rw [hWz, hz, smul_smul]

end CFSG.LocalAnalysis.WeakClosure81
end
end
