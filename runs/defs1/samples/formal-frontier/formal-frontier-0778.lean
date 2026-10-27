public section

open DirectSum

namespace GradedLocalization

universe u v w

variable {A : Type u} [CommRing A]

variable {ι : Type v} [DecidableEq ι] [AddCommGroup ι]

variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable (M : Submonoid A)

variable (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜)

/-- Projection onto degree `i` in a localization at homogeneous elements. -/
@[expose] noncomputable def projection (i : ι) : Localization M →+ Localization M where
  toFun := projectionFun 𝒜 M hM i
  map_zero' := by
    rw [← Localization.mk_zero (1 : M), projectionFun_mk 𝒜 M hM i
      (SetLike.one_mem_graded 𝒜)]
    simp
  map_add' x y := by
    refine Localization.induction_on₂ x y fun c d ↦ ?_
    obtain ⟨j, hcj⟩ := hM c.2.2
    obtain ⟨k, hdk⟩ := hM d.2.2
    rw [Localization.add_mk, projectionFun_mk 𝒜 M hM i hcj,
      projectionFun_mk 𝒜 M hM i hdk,
      projectionFun_mk 𝒜 M hM i
        (SetLike.GradedMul.mul_mem hcj hdk), Localization.add_mk]
    congr 1
    simp only [decompose_add, decompose_mul, DirectSum.add_apply, AddMemClass.coe_add,
      DirectSum.decompose_of_mem _ hcj, DirectSum.decompose_of_mem _ hdk]
    rw [show i + (j + k) = j + (i + k) by ac_rfl,
      DirectSum.coe_of_mul_apply_add]
    rw [show j + (i + k) = k + (i + j) by ac_rfl,
      DirectSum.coe_of_mul_apply_add]

end GradedLocalization
end
