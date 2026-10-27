public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace TauCeti.Contraction

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  (K : CochainComplex C ℤ) (U Z W : C)

namespace ThreeTermCancellationData

variable {K U Z W} (h : ThreeTermCancellationData K U Z W)

/-- The degree-zero projection after eliminating the two identity blocks. -/
def projectionZero : K.X 0 ⟶ Z :=
  h.zeroIso.hom ≫ (biprod.fst - pU ≫ delta h)

end ThreeTermCancellationData
end TauCeti.Contraction
end
end
