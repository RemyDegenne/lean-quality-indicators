@[expose] public section

section LatticeOrderedGroup

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

variable (x : X)

theorem isGLB_sup_const {A : Set X} {a : X} (x : X) (h : IsGLB A a) :
    IsGLB ((fun z => x ⊔ z) '' A) (x ⊔ a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact sup_le_sup_left (h.1 hz) x
  · intro u hu
    have hA : ∀ z ∈ A, u - (x - a)⁺ ≤ z := by
      intro z hz
      have hzu : u ≤ z + (x - z)⁺ := by
        rw [← sup_eq_add_posPart, sup_comm]; exact hu ⟨z, hz, rfl⟩
      have hmono : (x - z)⁺ ≤ (x - a)⁺ := posPart_mono (sub_le_sub_left (h.1 hz) x)
      exact sub_le_iff_le_add.mpr (hzu.trans (by gcongr))
    have key : u - (x - a)⁺ ≤ a := h.2 hA
    calc u = (u - (x - a)⁺) + (x - a)⁺ := by abel
      _ ≤ a + (x - a)⁺ := by gcongr
      _ = a ⊔ x := (sup_eq_add_posPart a x).symm
      _ = x ⊔ a := sup_comm _ _

end LatticeOrderedGroup
end
