namespace OAI

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

section

namespace VertexCover.Restriction.CompactCube

theorem realWeights_update {ι κ : Type*} [DecidableEq ι]
    (s : ι → κ → Interval) (j : ι) (x : κ → Interval) :
    realWeights (Function.update s j x) =
      Function.update (realWeights s) j (fun k => (x k).1) := by
  funext i k
  by_cases hi : i = j
  · subst i
    simp [realWeights]
  · simp [realWeights, Function.update_of_ne hi]

end VertexCover.Restriction.CompactCube
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
