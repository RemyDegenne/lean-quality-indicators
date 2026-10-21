namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node473 node473Labels = Sparse.eval singlePairValue473 (familyPairVector B) := by
  have hp := single_label_three B hB node473
  have hl : node473Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node473 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 1) = PairSemantics.raw5168 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node473 PairSemantics.raw5168; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5168 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 2) = PairSemantics.raw9006 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node473 PairSemantics.raw9006; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9006 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value717 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 3) = PairSemantics.raw5120 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node473 PairSemantics.raw5120; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5120 hH).trans (PairSemantics.sound717 hH)
  have hm4 : familyPairMoment B (groupedColumns node473 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2131 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node473 (EqualityPatterns.family3.label 4) = PairSemantics.raw3935 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node473 PairSemantics.raw3935; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3935 hH).trans (PairSemantics.sound2131 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue473, PairSemantics.value0, PairSemantics.value11, PairSemantics.value717, PairSemantics.value2131, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics
end OAI
