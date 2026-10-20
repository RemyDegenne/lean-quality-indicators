public section

namespace TauCeti

open CategoryTheory

section Sequence

universe u

variable (k : Type u) [Ring k] (G : Type*) (X : Type u) [Monoid G] [MulAction G X]

/-- The permutation augmentation sequence `ker(sum) → k[X] → k`. -/
noncomputable def permutationAugmentationSequence : ShortComplex (Rep k G) :=
  ShortComplex.mk (Rep.ofHom (augmentationSubrepresentation k G X).subtype)
    (permutationAugmentation k G X) (by
      ext v
      simpa [permutationAugmentation_apply k G X] using
        (mem_augmentationSubrepresentation_iff (k := k) (G := G)).mp v.2)

end Sequence
end TauCeti
end
