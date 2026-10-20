@[expose] public section

variable {α : Type*} {ι β : Sort _}

namespace Set

variable {S : ι → Set α} {f : ∀ i, S i → β}
  {hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  {hS : iUnion S = univ}

theorem preimage_liftCover (t : Set β) : liftCover S f hf hS ⁻¹' t = ⋃ i, (↑) '' f i ⁻¹' t := by
  change (iUnionLift S f hf univ hS.symm.subset ∘ fun a => ⟨a, mem_univ a⟩) ⁻¹' t = _
  rw [preimage_comp, preimage_iUnionLift]
  ext; simp

end Set
end
