open scoped Finset

@[expose] public section

noncomputable section

open Set LinearMap Submodule

section Fintype

variable {α M : Type*} (R : Type*) [Fintype α] [Semiring R] [AddCommMonoid M] [Module R M]

variable (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]

variable (v : α → M)

variable {S}

section SpanRange

variable {v} {x : M}

omit [Fintype α]

theorem Submodule.mem_span_image_iff_exists_fun {s : Set α} :
    x ∈ span R (v '' s) ↔ ∃ t : Finset α, ↑t ⊆ s ∧ ∃ c : t → R, ∑ i, c i • v i = x := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht, c, hx⟩ ↦ ?_⟩
  · obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp h
    refine ⟨l.support, hl, l ∘ (↑), ?_⟩
    rw [← hx]
    exact l.support.sum_coe_sort fun a ↦ l a • v a
  · rw [← hx]
    exact sum_smul_mem (span R (v '' s)) c fun a _ ↦ subset_span <| by aesop

end SpanRange
end Fintype
end
end
