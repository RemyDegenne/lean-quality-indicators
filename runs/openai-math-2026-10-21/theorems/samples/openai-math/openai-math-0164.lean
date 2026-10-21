namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem

universe u v w

noncomputable section

variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]

variable (S : SymmetricSystem.{u} P Γ)

theorem imageClassRelation_inj (h A B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ q, q ≤ p → ∀ y z C : S.Name,
      (S.imageClassRelation h A B).holds q y C →
      (S.imageClassRelation h A B).holds q z C → S.atomic.EqF q y z := by
  intro q hq y z C hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,a,ha,hay,hCa⟩ := hy r hrq
  obtain ⟨t,hts,b,hb,hbz,hCb⟩ := hz s (hsr.trans hrq)
  have htp := hts.trans (hsr.trans (hrq.trans hq))
  have ham := S.atomic.mem_mono hts ha
  have haym := S.app_mono hts hay
  have haa : S.atomic.MemF t a (S.relationClass A (S.kernelGraph h A B) a) :=
    (S.mem_relationClass _ _ _ _ _).mpr ⟨ham,
      (S.app_kernelGraph_value hf htp ham haym a).mpr ⟨ham,haym⟩⟩
  have heab := S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hts hCa)) hCb
  have hab := (S.mem_relationClass _ _ _ _ _).mp
    ((S.atomic.mem_congr (S.atomic.eq_refl t a) heab).mp haa)
  have haz := ((S.app_kernelGraph_value hf htp hb hbz a).mp hab.2).2
  exact ⟨t,hts.trans hsr,S.mapsTo_unique hf htp ham haym haz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem
end OAI
