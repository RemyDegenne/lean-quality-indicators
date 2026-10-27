@[expose] public section

open scoped Topology

section Torsor

variable {V P α : Type*} [Group V] [TopologicalSpace V] [Torsor V P] [TopologicalSpace P]

export IsTopologicalAddTorsor (continuous_vsub)

export IsTopologicalTorsor (continuous_sdiv)

variable [IsTopologicalTorsor P]

variable [TopologicalSpace α]

/-- `Equiv.pointReflection` as a homeomorphism -/
def Homeomorph.pointReflection {V P : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P]
    [TopologicalSpace P] [IsTopologicalAddTorsor P] (p : P) : P ≃ₜ P :=
  (Homeomorph.constVSub p).trans (Homeomorph.vaddConst p)

end Torsor
end
