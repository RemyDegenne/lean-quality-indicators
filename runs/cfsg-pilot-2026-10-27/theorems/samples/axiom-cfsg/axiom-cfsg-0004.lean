public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem cTilde_le_centSection {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hNL : D.M ≤ normalizer (L : Set G))
    (hsimple : IsSimpleGroup (Bar2 L)) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    F11.CTilde D.M V₀ V ≤ centSection D.M L (pCoreOf 2 L) := by
  intro c hc
  have hV := h.isElemAbelian
  have hMnorm := h.pairFacts.le_normalizer
  have hMnorm₀ := h.pairFacts.le_normalizer₀
  have hcM : c ∈ D.M := cTilde_le_M D.M V₀ V hc
  have hLM : L ≤ D.M := hL.1.le
  have hCtN : D.M ≤ normalizer (F11.CTilde D.M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M D.M V₀ V)).mp
      (cTilde_subgroupOf_normal hV hMnorm hMnorm₀)
  refine ⟨hcM, hNL hcM, UC6S846.normalizer_le_normalizer_pCoreOf L (hNL hcM), fun a ha => ?_⟩
  have haL : c * a * c⁻¹ * a⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNL hcM) a).1 ha) (L.inv_mem ha)
  have h1 : a * c⁻¹ * a⁻¹ ∈ F11.CTilde D.M V₀ V :=
    (Subgroup.mem_normalizer_iff.mp (hCtN (hLM ha)) c⁻¹).1 (inv_mem hc)
  have hC : c * a * c⁻¹ * a⁻¹ ∈ F11.CTilde D.M V₀ V := by
    have h2 : c * a * c⁻¹ * a⁻¹ = c * (a * c⁻¹ * a⁻¹) := by group
    rw [h2]
    exact mul_mem hc h1
  obtain ⟨-, hs, hact⟩ := (mem_cTilde_iff hV hMnorm).1 hC
  exact mem_pCoreOf_of_actTil_eq_one h hL.1 hsimple hL1 haL hs hact

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
end
