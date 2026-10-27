@[expose] public section

universe w'' w' w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace PreZeroHypercover

variable {S T : C} (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} S)

/-- Replace the indexing type of a pre-`0`-hypercover. -/
@[simps!]
def reindex (E : PreZeroHypercover.{w} T) {ι : Type w'} (e : ι ≃ E.I₀) :
    PreZeroHypercover.{w'} T :=
  E.restrictIndex e

end PreZeroHypercover
end CategoryTheory
end
