@[expose] public section

open scoped ContDiff Manifold

open Set TopologicalSpace RS.Cech

namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

variable (ψ : ∀ p : X, RS.MeroGermOn X (chartAt ℂ p).source) (S : Finset X)

variable (D : RS.Divisor X)

variable (D' : RS.Divisor X) (hD'mem : ∀ p ∈ S, DPrimeOf D p (ψ p) ≤ D')

variable {𝒱 : RS.Cech.FinCover (⊤ : Opens X)} (h𝒱Adapted : 𝒱.IsAdapted S)
  (hOclause : ∀ p ∈ S, ∀ k, p ∈ 𝒱.U k → 𝒱.U k ≤ injPatch ψ S D p)

open scoped Classical in
include ψ S D D' hD'mem hOclause in
omit [ConnectedSpace X] in
theorem injG_apply_of_not_mem (T : Finset X) (k : Fin 𝒱.n) (hnot : ∀ p ∈ T, p ∈ S → p ∉ 𝒱.U k) :
    injG ψ S D D' hD'mem hOclause T k = 0 := by
  change (if h : ∃ p ∈ T ∩ S, p ∈ 𝒱.U k then _ else _) = _
  rw [dite_eq_right]
  rintro ⟨q, hqTS, hqk⟩
  exact hnot q (Finset.mem_of_mem_inter_left hqTS) (Finset.mem_of_mem_inter_right hqTS) hqk

end RS.LaurentTail
end
