namespace OAI

open Set Filter MeasureTheory Finset

open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuousOn_coordinateWedges
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (f : ℕ → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω) (n : ℕ) :
    ContinuousOn (coordinateWedges f n) Ω := by
  have hx (i : ℕ) : ContinuousOn (fun z => (planarGradient (f i) z).1) Ω :=
    ((hf i).fderiv_of_isOpen (m := ∞) hΩ (by simp)).continuousOn.clm_apply continuousOn_const
  have hy (i : ℕ) : ContinuousOn (fun z => (planarGradient (f i) z).2) Ω :=
    ((hf i).fderiv_of_isOpen (m := ∞) hΩ (by simp)).continuousOn.clm_apply continuousOn_const
  unfold coordinateWedges covectorWedges
  apply continuousOn_finsetSum
  intro j _
  apply continuousOn_finsetSum
  intro i _
  exact ((hx i).mul (hy j) |>.sub ((hx j).mul (hy i))).abs

end CircleDomainRigidity.FiniteTransfer
end
end OAI
