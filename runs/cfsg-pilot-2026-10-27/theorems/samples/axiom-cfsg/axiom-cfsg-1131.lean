public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem isS0_of_reflTransGen {p : ℕ} (h49 : Lemma49At G p) {t t' : Triple G}
    (h : Relation.ReflTransGen (PumpRel p) t t') (ht : IsS0 p t.1 t.2.1 t.2.2) :
    IsS0 p t'.1 t'.2.1 t'.2.2 := by
  induction h with
  | refl => exact ht
  | @tail u u' _ hstep ih =>
    refine ⟨hstep.2.1, le_antisymm (tripleLevel_le_dLevel hstep.2.1) ?_⟩
    rw [← ih.2]
    exact tripleLevel_le_of_pumpRel h49 hstep

end CFSG.LocalAnalysis.GLTheoremA
end
