public section

namespace TauCeti

section Lift

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P] (hP : IsProP 2 P) (a s y : P)
  (h : a ^ 2 * s ^ 4 * (s⁻¹ * y⁻¹ * s * y) = 1)

/-- **The universal property of `D₀`**: three elements `a, s, y` of a pro-`2` group `P` satisfying
`a²s⁴(s,y) = 1` determine a continuous homomorphism `D₀ → P` with `A ↦ a`, `S ↦ s`, `Y ↦ y`. -/
noncomputable def d0Lift : demushkinD0 →ₜ* P :=
  presentedProP.lift (freeProP.lift hP ![a, s, y]) fun r hr ↦ by
    rw [Set.mem_singleton_iff.mp hr]
    simpa [d0Relator] using h

end Lift
end TauCeti
end
