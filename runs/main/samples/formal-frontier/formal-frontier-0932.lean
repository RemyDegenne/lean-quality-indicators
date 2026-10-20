public section

open CategoryTheory

namespace FiniteGroupTateCohomology

universe u v w

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Fintype G]

section Quotient

variable {H : Type v} [Group H]

variable (A : Rep.{w} R H) (S : Subgroup H) [S.Normal] [Fintype S]

@[reassoc]
lemma quotientNorm_naturality {B : Rep.{w} R H} (f : A ⟶ B) :
    quotientNorm A S ≫ (Rep.quotientToInvariantsFunctor R S).map f =
      (Rep.quotientToCoinvariantsFunctor R S).map f ≫ quotientNorm B S := by
  ext x
  apply Subtype.ext
  change f.hom ((Rep.norm (Rep.res S.subtype A)).hom x) =
    (Rep.norm (Rep.res S.subtype B)).hom (f.hom x)
  simpa using congrArg (fun q => q.hom x)
    (Rep.norm_comm ((Rep.resFunctor S.subtype).map f)).symm

end Quotient
end FiniteGroupTateCohomology
end
