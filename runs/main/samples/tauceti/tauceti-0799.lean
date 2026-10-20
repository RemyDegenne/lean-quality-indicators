public section

open Order AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}}

noncomputable section

@[simp]
lemma mem_finiteCodimensionOneCycles_iff {C : AlgebraicCycle X ℤ} :
    C ∈ finiteCodimensionOneCycles X ↔
      C.support.Finite ∧ ∀ x ∈ C.support, coheight x = 1 :=
  Iff.rfl

end
end SchemeWeilDivisor
end AlgebraicGeometry
end TauCeti
end
