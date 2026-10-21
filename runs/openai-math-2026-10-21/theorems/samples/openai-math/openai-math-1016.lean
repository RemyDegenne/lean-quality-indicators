namespace OAI

namespace MatchingFPRAS.ExecutableSource

open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder

open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling

attribute [local instance] NumberedHierarchy.labelOrder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

variable {n : ℕ} [Nontrivial (Fin n)]

lemma numericMarks_selected {E : Type} [Fintype E] [LinearOrder E]
    (s : Finset E) (m : E→Fin 3) (de : DecidableEq E) :
    numericMarks s (@selectedMarks E de s (fun e=>m e.val))=numericMarks s m := by
  unfold numericMarks
  apply List.map_congr_left
  intro e he
  have hm : e∈s := (Finset.mem_sort _).mp he
  simp only [selectedMarks,hm,↓reduceDIte]

end MatchingFPRAS.ExecutableSource
end OAI
