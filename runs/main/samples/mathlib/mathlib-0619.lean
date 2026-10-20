@[expose] public section

variable {K : Type*} [DivisionRing K] [TopologicalSpace K]

variable (K)

section LocalExtr

variable {α β : Type*} [TopologicalSpace α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β] {a : α}

open scoped Topology

theorem IsLocalMin.inv {f : α → β} {a : α} (h1 : IsLocalMin f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax f⁻¹ a := by
  filter_upwards [h1, h2] with z h3 h4 using (inv_le_inv₀ h4 h2.self_of_nhds).mpr h3

end LocalExtr
end
