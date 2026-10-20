public noncomputable section

open Cardinal FiniteArchimedeanClass

open scoped HahnSeries NatOrdinal

universe u

namespace ConwayRefinement.Standalone.Oz

theorem conwayConjecture_iff_forall_isPrimal :
    ConwayConjecture.{u} ↔ ∀ b : Surreal.OmnificInteger.{u}, IsPrimal b := by
  rw [conwayConjecture_iff_native, conwayRefinementConjecture_def,
    ← hasFourFactorRefinement_def, hasFourFactorRefinement_iff_forall_isPrimal]

end ConwayRefinement.Standalone.Oz
end
