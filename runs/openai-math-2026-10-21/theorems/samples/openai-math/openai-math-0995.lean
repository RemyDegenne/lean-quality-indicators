namespace OAI

noncomputable section

universe u v w z

namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [PartialOrder E] {B : Type v} [PartialOrder B]
  {D : OmegaCategory.{w}}

lemma posetOneFunctor_naturality_obj (hD : D.IsTruncated 1) (f : E →o B)
    (F : OmegaCategory.Functor (complex B).nu D) (a : E) :
    (posetOneFunctor hD (OmegaCategory.Functor.comp (complexMap f).nu F)).obj a =
      (f.monotone.functor ⋙ posetOneFunctor hD F).obj a := by
  apply Subtype.ext
  exact congrArg F.map (complexMap_vertex f a)

end Thomason.NormalizedChains.PosetTables
end
end OAI
