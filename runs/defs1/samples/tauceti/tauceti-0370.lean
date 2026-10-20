public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] {S S₁ S₂ : ShortComplex C}

namespace IsKernelCokernelPair

section Factorizations

variable {A : C}

/-- The factorization through the cokernel `S.g` of a morphism out of `S.X₂` killed by `S.f`. -/
noncomputable def desc (h : IsKernelCokernelPair S) (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
    S.X₃ ⟶ A :=
  (CokernelCofork.IsColimit.desc' h.gIsCokernel k hk).1

end Factorizations
end IsKernelCokernelPair
end HasZeroMorphisms
end TauCeti
end
