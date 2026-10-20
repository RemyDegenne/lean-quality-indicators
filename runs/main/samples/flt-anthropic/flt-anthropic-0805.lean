namespace P2MW.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField

open IntermediateField

namespace AlgebraicCurve

namespace SeparatingTranscendentalOfPerfectField

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isAlgebraic_adjoin_of_transcendental {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic K⟮t⟯ F := by
  classical
  have htind : AlgebraicIndepOn K id ({t} : Set F) := by
    refine algebraicIndependent_unique_type_iff.mpr ?_
    simpa using ht
  obtain ⟨s, hts, hbasis⟩ := exists_isTranscendenceBasis_superset htind
  have hcard := hbasis.lift_cardinalMk_eq (isTranscendenceBasis_of_transcendental hx hfd)
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hsub : s.Subsingleton := Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le
  have hseq : s = {t} := hsub.eq_singleton_of_mem (hts rfl)
  subst hseq
  have h := hbasis.isAlgebraic_field
  rwa [Subtype.range_coe] at h

end SeparatingTranscendentalOfPerfectField
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField
