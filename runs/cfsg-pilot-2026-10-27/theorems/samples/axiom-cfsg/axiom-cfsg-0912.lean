public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer

open scoped Pointwise

section Transport

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}

variable {e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He}

omit [Finite X] in
theorem mem_imN {U : Subgroup X} (hU : U ≤ normalizer (L : Set X))
    {y : Equiv.Perm (Fin 8330)} : y ∈ imN e U ↔ ∃ x ∈ U, heN e x = y := by
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l, hl, by rw [heN_of_mem l.2]; rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨heModelN e ⟨x, hU hx⟩, ⟨⟨x, hU hx⟩, hx, rfl⟩, by rw [heN_of_mem (hU hx)]; rfl⟩

end Transport
end CFSG.ComponentClassification.GrSLit
end
