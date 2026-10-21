namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem

universe u v w

variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]

variable (S : SymmetricSystem.{u} P Γ)

theorem mem_union (σ ν : S.Name) (p : P) : S.atomic.MemF p ν σ.union ↔
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ χ : S.Name,
      S.atomic.MemF r χ σ ∧ S.atomic.MemF r ν χ := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp h) q hqp
    obtain ⟨χ,a,b,ha,hb,hca,hcb⟩ := (S.edge_union σ τ c).mp he
    refine ⟨r,hrq,χ,S.mem_of_edge ha (hrc.trans hca),?_⟩
    exact (S.atomic.mem_congr heq (S.atomic.eq_refl r χ)).mpr
      (S.mem_of_edge hb (hrc.trans hcb))
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,χ,hχ,hν⟩ := h q hqp
    obtain ⟨s,hsr,τ,c,hτ,hsc,heq⟩ := (S.mem_iff.mp hχ) r le_rfl
    have hντ : S.atomic.MemF s ν τ :=
      (S.atomic.mem_congr (S.atomic.eq_refl s ν) heq).mp (S.atomic.mem_mono hsr hν)
    obtain ⟨t,hts,η,d,hη,htd,heq'⟩ := (S.mem_iff.mp hντ) s le_rfl
    exact ⟨t,hts.trans (hsr.trans hrq),η,t,
      (S.edge_union σ η t).mpr ⟨τ,c,d,hτ,hη,hts.trans hsc,htd⟩,le_rfl,heq'⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem
end OAI
