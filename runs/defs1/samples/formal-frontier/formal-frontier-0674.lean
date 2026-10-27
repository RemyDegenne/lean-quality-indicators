public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

/-- The coefficient norm for finite negative deflation, typed over the direct
quotient homomorphism from `G / S` to `G / T`. -/
@[expose]
noncomputable def finiteNegativeDeflationCoeffDirect (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    A.quotientToInvariants S ⟶
      Rep.res (finiteDeflationGroupHom S T hST) (A.quotientToInvariants T) :=
  let coeff := Rep.toCoinvariantsMkQ (A.quotientToInvariants S)
      (T.map (QuotientGroup.mk' S)) ≫
    (Rep.resFunctor (QuotientGroup.mk' (T.map (QuotientGroup.mk' S)))).map
      (FiniteGroupTateCohomology.quotientNorm (A.quotientToInvariants S)
          (T.map (QuotientGroup.mk' S)) ≫
        (nestedQuotientInvariantsRepIso A S T hST).hom)
  Rep.ofHom ⟨coeff.hom.toLinearMap, fun g ↦ by
    change _ =
      (A.quotientToInvariants T).ρ (finiteDeflationGroupHom S T hST g) ∘ₗ _
    rw [← thirdIso_comp_quotient_mk S T hST]
    exact coeff.hom.isIntertwining' g⟩

end ContinuousGroupCohomology
end
