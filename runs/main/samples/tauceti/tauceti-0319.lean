public section

open CategoryTheory CategoryTheory.Limits TauCeti

namespace CategoryTheory.ShortComplex.IsAlmostSplit

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
  {S : ShortComplex C}
  [IsLocalRing (End S.X₁)] [IsLocalRing (End S.X₃)]

variable (k : Type*) [Ring k] [Linear k C]

theorem rightRadicalQuotientEquiv_symm_mk (hS : S.IsAlmostSplit) (X : C)
    (a : jacobsonRadicalSubmodule k X S.X₃) (b : X ⟶ S.X₂) (hb : b ≫ S.g = a) :
    (hS.rightRadicalQuotientEquiv k X).symm (irreducibleMorphismMk k X S.X₃ a) =
      Submodule.Quotient.mk b := by
  apply (hS.rightRadicalQuotientEquiv k X).injective
  simp only [LinearEquiv.apply_symm_apply, rightRadicalQuotientEquiv_mk]
  exact congrArg (irreducibleMorphismMk k X S.X₃) (Subtype.ext hb.symm)

end CategoryTheory.ShortComplex.IsAlmostSplit
end
