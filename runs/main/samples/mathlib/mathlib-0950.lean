@[expose] public section

open Function

universe u u' u'' v

variable {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

namespace SetLike

open SMulMemClass

section SMul

variable [SMul R M] [SetLike S M] [hS : SMulMemClass S R M] (s : S)

open scoped Pointwise in
@[to_additive]
theorem smul_subset_self {S R M : Type*} [SetLike S M] [SMul R M] [SMulMemClass S R M]
    (r : R) (s : S) : (r • s : Set M) ⊆ s := by
  rintro _ ⟨x, hx, rfl⟩
  simpa using SMulMemClass.smul_mem (r : R) hx

end SMul
end SetLike
end
