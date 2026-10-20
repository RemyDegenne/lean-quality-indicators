public section

open Multiplicative Set Topology

open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)
  (m : IntegralCharacter N) (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1)

/-- The holomorphic monomial function of an integral character nonnegative on every cone.
Its restriction to each affine chart is evaluation on the corresponding monomial. -/
noncomputable def analyticCharacter : C(Φ.analyticRealization hΦ, ℂ) where
  toFun := Φ.characterFun hΦ m hm
  continuous_toFun := by
    apply continuous_def.2
    intro s hs
    rw [Φ.isOpen_iff_forall_preimage_analyticAffineChartι hΦ]
    intro σ
    have heq : Φ.characterFun hΦ m hm ∘ Φ.analyticAffineChartι hΦ σ =
        Φ.chartCharacter m hm σ := funext (Φ.characterFun_analyticAffineChartι hΦ m hm σ)
    rw [← preimage_comp, heq]
    let _ := affinePointTopology (Φ.analyticChartGenerators σ).2
    have hc := continuous_apply_single (Φ.analyticChartGenerators σ).2 ⟨m, hm σ⟩
    rw [← Φ.analyticAffineChart_str_eq σ] at hc
    exact hc.isOpen_preimage s hs

end TauCeti.Toric.Fan
end
