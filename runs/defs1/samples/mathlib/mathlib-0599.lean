@[expose] public section

noncomputable section

open Finset Function Module

open scoped Affine

namespace Affine

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AffineSpace V P] [AffineSpace V₂ P₂] [AffineSpace V₃ P₃]

namespace Simplex

variable {P P₂ P₃}

variable {k}

/-- The face of a simplex with all but one point. -/
def faceOpposite {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : Simplex k P (n - 1) :=
  s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le])

end Simplex
end Affine
end
end
