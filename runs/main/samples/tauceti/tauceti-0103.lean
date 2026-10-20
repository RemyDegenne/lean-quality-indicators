public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] [Invertible (2 : K)]

@[simp, reassoc (attr := simp)]
theorem kummerCoeffIsoTrivialF2_hom_comp_h2MuToUnits :
    ContinuousCohomology.coeffMap (kummerCoeffIsoTrivialF2 K).hom 2 ≫ h2MuToUnits K =
      h2KummerToUnits K 2 :=
  Iso.hom_inv_id_assoc
    ((ContinuousCohomology.continuousCohomologyFunctor ℤ (AbsoluteGaloisGroup K) 2).mapIso
      (kummerCoeffIsoTrivialF2 K)) _

end TauCeti
end
end
