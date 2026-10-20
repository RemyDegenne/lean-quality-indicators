public section

open Set

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {x : X} {s s₁ s₂ t : Set X}

section Closure

theorem Filter.HasBasis.lift'_closure_eq_self {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) (hc : ∀ i, p i → IsClosed (s i)) : l.lift' closure = l :=
  le_antisymm (h.ge_iff.2 fun i hi => (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
    l.le_lift'_closure

end Closure
end
