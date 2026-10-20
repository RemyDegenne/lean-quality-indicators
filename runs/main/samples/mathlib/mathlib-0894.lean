@[expose] public section

noncomputable section

open Filter Set Topology

open scoped Uniformity

section TypeAlias

@[inherit_doc] scoped[UniformConvergence] notation:25 α " →ᵤ " β:0 => UniformFun α β

@[inherit_doc] scoped[UniformConvergence] notation:25 α " →ᵤ[" 𝔖 "] " β:0 => UniformOnFun α β 𝔖

open UniformConvergence

variable {α β : Type*} {𝔖 : Set (Set α)}

@[simp] lemma UniformFun.ofFun_toFun (f : α →ᵤ β) : ofFun (toFun f) = f := rfl

end TypeAlias
end
end
