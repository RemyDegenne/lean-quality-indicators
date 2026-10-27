@[expose] public section

open scoped ContDiff Manifold

open Set TopologicalSpace RS.Cech

namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-- The Mittag-Leffler class in `H¹(D)` of a germ `ψ` at the point `p`. -/
noncomputable def mlClassAt (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.Cech.H1 D :=
  mlClassAtOf p D (DPrimeOf D p ψ) ψ (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ)
    (cleanNbhd_sub_source D p ψ) (cleanNbhd_ord_nonneg D p ψ) (cleanNbhd_D_eq_zero D p ψ)
    (ψVOf D p ψ) rfl

end RS.LaurentTail
end
