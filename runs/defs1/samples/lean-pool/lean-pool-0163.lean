@[expose] public section

noncomputable section

open scoped unitInterval Topology NNReal

open Asymptotics Filter Set Metric Function

local notation "dim" => Module.finrank ℝ

namespace Moreira2001

section

universe x u v w

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {k : ℕ} {α : I} {s : Set (E × F)} {a : E × F} {f : E × F → ℝ}

/-- Implicit-function data used to build a local Moreira chart at a non-large point. -/
@[irreducible]
def chartImplicitData (f : E × F → ℝ) (a : E × F)
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    ImplicitFunctionData ℝ (E × F) ℝ (E × (fderiv ℝ f a ∘L .inr ℝ E F).ker) where
  leftFun := f
  leftDeriv := fderiv ℝ f a
  hasStrictFDerivAt_leftFun := hfa.contDiffAt.hasStrictFDerivAt <| mod_cast hk
  rightFun := _
  rightDeriv := .prodMap (.id _ _) (Submodule.ClosedComplemented.of_finiteDimensional _).choose
  hasStrictFDerivAt_rightFun := ContinuousLinearMap.hasStrictFDerivAt _
  pt := a
  range_leftDeriv := by
    refine IsSimpleOrder.eq_bot_or_eq_top _ |>.resolve_left ?_
    rw [LinearMap.range_eq_bot, ← ContinuousLinearMap.toLinearMap_zero, ContinuousLinearMap.coe_inj]
    contrapose! hdf
    rw [hdf, ContinuousLinearMap.zero_comp]
  range_rightDeriv := by
    have : (Submodule.ClosedComplemented.of_finiteDimensional <|
        (fderiv ℝ f a ∘L .inr ℝ E F).ker).choose.range = ⊤ := by
      apply LinearMap.range_eq_of_proj
      exact Exists.choose_spec (_ : Submodule.ClosedComplemented _)
    rw [ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap, this]
    simpa using (Submodule.prod_top :
      (Submodule.prod (⊤ : Submodule ℝ E) (⊤ : Submodule ℝ (fderiv ℝ f a ∘L .inr ℝ E F).ker)) = ⊤)
  isCompl_ker := by
    have H : (fderiv ℝ f a ∘L .inr ℝ E F).ker.ClosedComplemented :=
      .of_finiteDimensional _
    constructor
    · rw [Submodule.disjoint_def]
      rintro ⟨x, y⟩ hker hmap
      have hx : x = 0 := congrArg Prod.fst hmap
      have hy : H.choose y = 0 := congrArg Prod.snd hmap
      refine Prod.ext hx ?_
      lift y to (fderiv ℝ f a ∘L .inr ℝ E F).ker using by simpa [hx] using hker
      have hy' : (y : F) = 0 := by
        have hchoose : ((H.choose (y : F) : (fderiv ℝ f a ∘L .inr ℝ E F).ker) : F) = 0 := by
          simpa using congrArg Subtype.val hy
        exact (congrArg Subtype.val (H.choose_spec y)).symm.trans hchoose
      simpa using hy'
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      rintro ⟨x, y⟩
      obtain ⟨z, hz⟩ : ∃ z : F, fderiv ℝ f a (x, z) = 0 := by
        have : (fderiv ℝ f a ∘L .inr ℝ _ _).range = ⊤ := by
          refine IsSimpleOrder.eq_bot_or_eq_top _ |>.resolve_left ?_
          rwa [LinearMap.range_eq_bot, ← ContinuousLinearMap.toLinearMap_zero,
            ContinuousLinearMap.coe_inj]
        rw [Submodule.eq_top_iff'] at this
        refine this (-fderiv ℝ f a (x, 0)) |>.imp fun z hz ↦ ?_
        rw [← (x, z).fst_add_snd, map_add]
        simpa [eq_neg_iff_add_eq_zero, add_comm] using hz
      rcases Submodule.codisjoint_iff_exists_add_eq.mp
        (LinearMap.isCompl_of_proj H.choose_spec).codisjoint (y - z)
        with ⟨w, t, hw, ht, hsub⟩
      refine ⟨(x, w + z), (0, t), ?_, ?_, ?_⟩
      · rwa [← zero_add x, ← Prod.mk_add_mk, LinearMap.mem_ker, map_add,
          ContinuousLinearMap.coe_coe, hz, add_zero]
      · change (0, H.choose t) = (0 : E × (fderiv ℝ f a ∘L .inr ℝ E F).ker)
        exact Prod.ext rfl ht
      · rw [Prod.mk_add_mk, add_zero, add_right_comm w z t, hsub, sub_add_cancel]

end
end Moreira2001
end
end
