public section

open scoped IntermediateField

open KaehlerDifferential

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k]
  (P : Place k F) (hP : P.degree = 1) (hF : IsFunctionField k F)
  (hex : IsIntegrallyClosedIn k F)
  {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]

theorem mem_range_map_iff_forall_repartitionDualComponent_eq_zero (ω : Ω[F⁄k]) :
    ω ∈ (KaehlerDifferential.map k k P.integers F).range ↔
      ∀ u ∈ P.integers,
        repartitionDualComponent
          (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω :
            Module.Dual k ↥(repartitionSpace k F)) P u = 0 := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  let := hsep
  have := P.finiteDimensional_residueField hF
  have := P.isSeparable_residueField_of_perfectField hF
  rw [P.mem_range_map_iff_coord_mem_integers ht htr,
    P.coord_mem_integers_iff_forall_traceResidue_coord_smul_eq_zero ht htr]
  simp_rw [P.traceResidue_coord_smul_eq_repartitionDualComponent hF hex hx ht htr]

end TauCeti.Place
end
