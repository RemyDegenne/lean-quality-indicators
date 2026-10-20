@[expose] public section

noncomputable section

open Topology TopologicalSpace Set Filter Function

universe u v u' v'

variable {X : Type u} {Y : Type v} {W Z ε ζ : Type*}

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  [TopologicalSpace ε] [TopologicalSpace ζ]

theorem prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s ∈ 𝓝 x) (hy : t ∈ 𝓝 y) :
    s ×ˢ t ∈ 𝓝 (x, y) :=
  prod_mem_nhds_iff.2 ⟨hx, hy⟩

end Prod
end
end
