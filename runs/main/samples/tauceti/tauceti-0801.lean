public section

namespace TauCeti

open CategoryTheory

universe u v

variable (A : Type u) [Ring A]

variable {A}

local notation "S" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))

local notation "T" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))

namespace FiniteProjectivePresentation

variable {M N L : ModuleCat.{max u v} A}

@[simp]
theorem stableTransposeIso_refl (P : FiniteProjectivePresentation M) :
    P.stableTransposeIso P = Iso.refl P.stableTransposeObj := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact AuslanderReitenTranspose.stableMap_id P.exact P.surjective

end FiniteProjectivePresentation
end TauCeti
end
