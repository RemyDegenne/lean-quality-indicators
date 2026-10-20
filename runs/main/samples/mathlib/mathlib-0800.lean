@[expose] public section

noncomputable section

open Filter Set Topology

open scoped Uniformity

open UniformConvergence

namespace UniformOnFun

variable {α β : Type*} {γ ι : Type*}

variable {s : Set α} {p : Filter ι}

local notation "𝒰(" α ", " β ", " u ")" => @UniformFun.uniformSpace α β u

variable (α β) [UniformSpace β] (𝔖 : Set (Set α))

local notation "𝒱(" α ", " β ", " 𝔖 ", " u ")" => @UniformOnFun.uniformSpace α β u 𝔖

variable {α β}

variable (α β)

theorem isUniformEmbedding_toFun_finite :
    IsUniformEmbedding (toFun _ : (α →ᵤ[{s | s.Finite}] β) → (α → β)) := by
  refine ⟨⟨?_⟩, Function.injective_id⟩
  simp_rw [Pi.uniformity, comap_iInf, comap_comap]
  refine HasBasis.ext (HasBasis.iInf' fun i ↦ (basis_sets _).comap _)
    (UniformOnFun.hasBasis_uniformity α β _ ⟨∅, finite_empty⟩
      (directedOn_of_sup_mem fun _ _ ↦ .union))
    (fun ⟨S, U⟩ ⟨hS, hU⟩ ↦ ⟨⟨S, ⋂ x ∈ S, U x⟩, ⟨⟨hS, biInter_mem hS |>.mpr hU⟩,
      fun f hf ↦ mem_iInter₂.mpr fun x hx ↦ mem_iInter₂.mp (hf x hx) x hx⟩⟩)
    (fun ⟨S, U⟩ ⟨hS, hU⟩ ↦ ⟨⟨S, fun _ ↦ U⟩, ⟨hS, fun _ _ ↦ hU⟩, fun f hf x hx ↦
      mem_iInter₂.mp hf x hx⟩)

end UniformOnFun
end
end
