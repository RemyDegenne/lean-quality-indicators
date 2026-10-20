public section

open Set Filter TopologicalSpace

open Filter Topology

variable {ι : Sort*} {α β X Y : Type*}

namespace Filter

theorem nhds_eq' (l : Filter α) : 𝓝 l = l.lift' fun s => { l' | s ∈ l' } := by
  simpa only [Function.comp_def, Iic_principal] using nhds_eq l

end Filter
end
