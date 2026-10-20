public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

lemma iInf_ker_eq_vanishingIdeal_iSup_closure_range
    (f : ∀ j, X j ⟶ Y) [∀ j, QuasiCompact (f j)] [∀ j, IsReduced (X j)] :
    (⨅ j, (f j).ker) = Scheme.IdealSheafData.vanishingIdeal (X := Y)
      (⨆ j, Closeds.closure (Set.range (f j))) := by
  rw [Scheme.IdealSheafData.vanishingIdeal_iSup]
  congr 1
  funext j
  exact (f j).ker_eq_vanishingIdeal_closure_range

end AlgebraicGeometry
end
end
