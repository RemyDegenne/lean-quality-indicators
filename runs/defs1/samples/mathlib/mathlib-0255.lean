@[expose] public section

noncomputable section

open CategoryTheory Category Limits Arrow

variable (V : Type*) [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

/-- If `V` is a preadditive category, then `RightFreyd V` is the category of arrows in `V`,
with morphisms identified when they are right homotopic. -/
def RightFreyd :=
  CategoryTheory.Quotient (rightHomotopic V)

end CategoryTheory.Preadditive
end
end
