public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [CommRing S] {w : S}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- Projection to the first summand. -/
noncomputable def biprodFst (X Y : MatrixFactorization S w) : biprod X Y ⟶ X :=
  ⟨CurvedDuplex.biprodFst X.obj Y.obj⟩

end TauCeti.MatrixFactorization
end
