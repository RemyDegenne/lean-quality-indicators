public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.LocalAnalysis.GLTheoremA.S10

open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma102_cover_equiv {p : ℕ} (hp : p.Prime) {I L : Subgroup G} (hIL : I ≤ L)
    (hsup : I ⊔ GLAPPrimeCoreOf p L = L) :
    ∃ F : PQuot p I ≃* PQuot p L, ∀ w : ↥I,
      F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL w) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hO_eq : GLAPPrimeCoreOf p I = I ⊓ GLAPPrimeCoreOf p L := (cover_facts hp hIL hsup).1
  have hOI : GLAPPrimeCore p ↥I ≤ (GLAPPrimeCore p ↥L).comap (Subgroup.inclusion hIL) := by
    intro w hw
    rw [Subgroup.mem_comap]
    have hw' : (w : G) ∈ GLAPPrimeCoreOf p I := (lemma102_mem_glaPPrimeCore_iff w.2).1 hw
    rw [hO_eq] at hw'
    exact (lemma102_mem_glaPPrimeCore_iff (hIL w.2)).2 hw'.2
  set F : PQuot p I →* PQuot p L :=
    QuotientGroup.map (GLAPPrimeCore p ↥I) (GLAPPrimeCore p ↥L) (Subgroup.inclusion hIL) hOI
    with hF
  have hFmk : ∀ w : ↥I, F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL w) :=
    fun w => QuotientGroup.map_mk _ _ _ _ _
  have hIO' : I ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    hIL.trans (le_normalizer_glaPPrimeCoreOf p L)
  have hFbij : Function.Bijective F := by
    refine ⟨(injective_iff_map_eq_one F).2 ?_, ?_⟩
    · intro q hq
      induction q using QuotientGroup.induction_on with
      | H w =>
        rw [hFmk, QuotientGroup.eq_one_iff] at hq
        rw [QuotientGroup.eq_one_iff]
        have hwO : (w : G) ∈ GLAPPrimeCoreOf p I := by
          rw [hO_eq]
          exact ⟨w.2, (lemma102_mem_glaPPrimeCore_iff (hIL w.2)).1 hq⟩
        exact (lemma102_mem_glaPPrimeCore_iff w.2).2 hwO
    · intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hl : (l : G) ∈ (I ⊔ GLAPPrimeCoreOf p L : Subgroup G) := hsup.symm ▸ l.2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _ hIO'] at hl
      obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hl
      refine ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
      rw [hFmk, QuotientGroup.eq]
      have hXO : y⁻¹ * (l : G) ∈ GLAPPrimeCoreOf p L := by
        rw [← hyz, inv_mul_cancel_left]
        exact hz
      exact (lemma102_mem_glaPPrimeCore_iff ((Subgroup.inclusion hIL ⟨y, hy⟩)⁻¹ * l).2).2 hXO
  exact ⟨MulEquiv.ofBijective F hFbij, fun w => hFmk w⟩

end S10
end CFSG.LocalAnalysis.GLTheoremA
end
