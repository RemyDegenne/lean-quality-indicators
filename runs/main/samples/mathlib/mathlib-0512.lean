@[expose] public section

noncomputable section

open Finset Function Module

open scoped Affine

namespace Affine

namespace Simplex

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

variable [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]

section PartialOrder

variable [PartialOrder k]

lemma affineCombination_mem_interior_face_iff_mem_Ioo {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w ∈ (s.face h).interior ↔
      (∀ i ∈ fs, w i ∈ Set.Ioo 0 1) ∧ (∀ i ∉ fs, w i = 0) :=
  affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

end PartialOrder
end Simplex
end Affine
end
end
