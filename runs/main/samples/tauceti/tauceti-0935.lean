public section

open Function Set Topology

namespace TauCeti

variable {X Y α : Type*} {k : ℕ}

section Ambient

variable {n : ℕ}

section Order

variable [LinearOrder α] {C : Set (Fin n → α)} {θ : Fin k → C → α}

section Map

variable {m : ℕ} (θ : Fin k → C → α) (f : (Fin m → α) → Fin n → α)

omit [LinearOrder α] in
theorem image_cylinder_sectionSet_comp (i : Fin k) :
    cylinder (f ⁻¹' C) '' sectionSet (fun i x ↦ θ i ⟨f x.1, x.2⟩) i =
      (fun y ↦ Fin.cons (y 0) (f (Fin.tail y))) ⁻¹' (cylinder C '' sectionSet θ i) := by
  ext y
  simp only [mem_image_cylinder, mem_sectionSet, mem_preimage, Fin.tail_cons, Fin.cons_zero]

end Map
end Order
end Ambient
end TauCeti
end
