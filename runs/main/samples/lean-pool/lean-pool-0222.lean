@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson

namespace KrauseLaceyShiftedLocalization

noncomputable
section

theorem krauseLaceyFixedScaleInput_eq_of_support_subset
    (S : Finset RealInterval) (f : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑S : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.centralThird))
    (hcover : Function.support f ⊆ ⋃ I ∈ S, I.centralThird) :
    krauseLaceyFixedScaleInput S f = f := by
  classical
  funext x
  by_cases hx : f x = 0
  · simp [krauseLaceyFixedScaleInput, Set.indicator_apply, hx]
  · have hxs : x ∈ Function.support f := hx
    rcases Set.mem_iUnion.1 (hcover hxs) with ⟨I, hxI⟩
    rcases Set.mem_iUnion.1 hxI with ⟨hIS, hxI⟩
    unfold krauseLaceyFixedScaleInput
    rw [Finset.sum_eq_single I]
    · exact Set.indicator_of_mem hxI f
    · intro J hJS hJI
      have hd := hdisj hIS hJS hJI.symm
      have hxJ : x ∉ J.centralThird := fun hxJ ↦ Set.disjoint_left.1 hd hxI hxJ
      simp [hxJ]
    · intro hn
      exact (hn hIS).elim

end
end KrauseLaceyShiftedLocalization
end QuadraticCarleson
end
