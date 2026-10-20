namespace P2MW.S_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Set Filter Topology

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace LanglandsTunnell

namespace CubicInduction

namespace UnipotentEntryHaar

p2m_open

open AutomorphicForm

section Measure

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace (GL (Fin 2) K)] [BorelSpace (GL (Fin 2) K)]

theorem isAddHaarMeasure_map_entry (μN : Measure ↥(unipotentGL2Hom (R := K)).range) [μN.IsHaarMeasure] :
    (μN.map entry).IsAddHaarMeasure where
  lt_top_of_isCompact := (IsFiniteMeasureOnCompacts.map μN entryHomeomorph).lt_top_of_isCompact
  open_pos := (continuous_entry.isOpenPosMeasure_map (μ := μN) entryHomeomorph.surjective).open_pos
  map_add_left_eq_self x := by
    have hme : Measurable (entry (K := K)) := continuous_entry.measurable
    rw [map_map (measurable_const_add x) hme]
    have hcomp : ((fun z => x + z) ∘ entry (K := K)) = entry ∘ fun y => ofEntry x * y := by
      funext y
      simp [Function.comp, entry_ofEntry_mul]
    rw [hcomp, ← map_map hme (measurable_const_mul _), map_mul_left_eq_self]

end Measure
end UnipotentEntryHaar
end CubicInduction
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq
