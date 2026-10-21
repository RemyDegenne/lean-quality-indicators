namespace OAI

open Set Filter Function MeasureTheory

open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_smooth_planar_cutoff {A O : Set ℂ}
    (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧
      ∀ᶠ z in 𝓝ˢ A, f z = 1 := by
  obtain ⟨V, hV, hAV, hVO, hVc⟩ :=
    exists_open_between_and_isCompact_closure hA hO hAO
  have hdisj : Disjoint Vᶜ A :=
    Set.disjoint_left.mpr (fun z hz hzA => hz (hAV hzA))
  obtain ⟨f, hzero, hone, hrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, ℂ))
      hV.isClosed_compl hA.isClosed hdisj (n := (⊤ : ℕ∞))
  have hsupp : Function.support (f : ℂ → ℝ) ⊆ V := by
    intro z hz
    by_contra hzV
    exact hz (hzero.self_of_nhdsSet z hzV)
  have htsupp : tsupport (f : ℂ → ℝ) ⊆ closure V := closure_mono hsupp
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, htsupp.trans hVO, hrange, hone⟩
  exact hVc.of_isClosed_subset isClosed_closure htsupp

end CircleDomainRigidity
end OAI
