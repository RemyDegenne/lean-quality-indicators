namespace OAI

namespace WitnessedSeparation.Grid

noncomputable section

open Classical Support

variable {n : ℕ} {b : Vertex n → Scalar}

namespace CycleFrame

variable (C : CycleFrame n)

lemma joint_incident (i j : Fin 4) (h : AdjacentIndex i j) :
    incident (C.joint i j) (C.edge i) ∧ incident (C.joint i j) (C.edge j) := by
  unfold joint
  split_ifs with he
  · subst j
    exact ⟨(C.incident_ends i).2,(C.incident_ends (i+1)).1⟩
  · have hi : i=j+1 := h.resolve_left he
    subst i
    exact ⟨(C.incident_ends (j+1)).1,(C.incident_ends j).2⟩

end CycleFrame
end
end WitnessedSeparation.Grid
end OAI
