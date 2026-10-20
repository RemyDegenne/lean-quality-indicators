@[expose] public section

open LinearMap Set Convex

variable {𝕜 E F α β : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section OrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 α] [SMul 𝕜 β] (s : Set E) (f : E → β) {g : β → α}

variable {𝕜 s f}

open OrderDual (toDual ofDual)

theorem StrictConvexOn.subset {t : Set E} (hf : StrictConvexOn 𝕜 t f) (hst : s ⊆ t)
    (hs : Convex 𝕜 s) : StrictConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

end SMul
end OrderedAddCommMonoid
end AddCommMonoid
end OrderedSemiring
end
