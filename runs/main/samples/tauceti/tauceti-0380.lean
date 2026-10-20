public section

noncomputable section

namespace CategoryTheory

open Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {S S' : ShortComplex C}

namespace ShortComplex

lemma isZero_resolutionComplex_X_add_two (S : ShortComplex C) (n : ℕ) :
    IsZero (S.resolutionComplex.X (n + 2)) :=
  isZero_zero C

end ShortComplex
end CategoryTheory
end
end
