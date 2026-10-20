public section

namespace TauCeti

open ContCohomology groupCohomology

open CategoryTheory

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable [IsGalois K L]

theorem subsingleton_H1_forcedDiscrete : Subsingleton (H1 Gal(L/K) (ForcedDiscrete L)) :=
  subsingleton_H1_of_forall_openNormalSubgroup fun U => subsingleton_of_forall_eq 0 fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      exact H1pi_eq_zero_iff.2 (mem_B1_iff.2
        (isCoboundary₁_of_isCocycle₁_of_quotient_to_fixedPoints_forcedDiscrete U
          (mem_Z1_iff.1 z.2).2))

end Galois
end TauCeti
end
