public section

namespace UniformSpace.Completion

section MapRingEquiv

variable {α β : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
  [Ring β] [UniformSpace β] [IsTopologicalRing β] [IsUniformAddGroup β]

theorem continuous_mapRingEquiv (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm) :
    Continuous (mapRingEquiv f hf hf') :=
  continuous_map.congr fun x ↦ (mapRingEquiv_apply f hf hf' x).symm

end MapRingEquiv
end UniformSpace.Completion
end
