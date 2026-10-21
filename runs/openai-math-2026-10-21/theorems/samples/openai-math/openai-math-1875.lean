namespace OAI

noncomputable section

namespace ContinuumCoulomb.QuantumCircuitCode

theorem rowStage_eq (rows width start : ℕ) (h : start < rows) (g : QMAGate) :
    qmaRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width ⟨start,by omega⟩)
      (qmaGridQubit rows width ⟨start+1,by omega⟩)
      (qmaSweepOrder width (rows-1-start)) g=rowStage rows width start g := by
  unfold qmaRowStage rowStage
  dsimp only
  rw [rowCut_eq,transferList_eq,transferList_eq,List.map_take,List.map_drop]
  have hp := rowPairs_eq rows width ⟨start,h⟩ (rows-1-start)
  simp only [Fin.castSucc_mk,Fin.succ_mk] at hp
  rw [hp,mapToRow_eq]

end ContinuumCoulomb.QuantumCircuitCode
end
end OAI
