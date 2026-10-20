public section

noncomputable section

open CategoryTheory Limits Opposite Finset

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {ι : Type w} [LinearOrder ι]

namespace Functor

variable (F : (Finset ι)ᵒᵖ ⥤ C)

/-- The summand inclusions `Functor.orderedCechComplexι` exhibit the degree `p` term of the ordered
Čech complex as the coproduct of the `F(s)` over the sets `s` with `p + 1` elements. -/
def isColimitOrderedCechComplexCofan (p : ℕ) :
    IsColimit (Cofan.mk (F.orderedCechComplex.X p) (F.orderedCechComplexι (p := p))) :=
  coproductIsCoproduct _

end Functor
end CategoryTheory
end
end
