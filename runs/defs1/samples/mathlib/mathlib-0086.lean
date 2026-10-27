@[expose] public section

open AffineSubspace Set Topology

open scoped Pointwise

variable {𝕜 V W Q P : Type*}

section AddTorsor

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x : P}

/-- The intrinsic frontier of a set is its frontier considered as a set in its affine span. -/
def intrinsicFrontier (s : Set P) : Set P :=
  (↑) '' frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

end AddTorsor
end
