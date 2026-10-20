@[expose] public section

section

open UniformSpace Filter Set Topology Function

open scoped Uniformity UniformConvergence

variable {ι κ X X' Y α α' β β' γ : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
  [uα : UniformSpace α] [uβ : UniformSpace β] [uγ : UniformSpace γ]

theorem equicontinuous_iff_range {F : ι → X → α} :
    Equicontinuous F ↔ Equicontinuous ((↑) : range F → X → α) :=
  forall_congr' fun _ => equicontinuousAt_iff_range

end
end
