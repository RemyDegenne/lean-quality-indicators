namespace OAI

namespace PartitionPilot.Forcing

section

universe u

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}

variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

theorem inside_entry_iff (i j : {i : ZFSet.{u} // i ∈ I}) (q t : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) (ZFSet.pair j.val t) ∈ batchAttachmentInsideGraph I Qs rs ↔
      i = j ∧ q ∈ d.space i ∧ t ∈ d.space i ∧ ZFSet.pair q t ∈ d.rel i := by
  rw [pair_mem_batchAttachmentInsideGraph]
  constructor
  · rintro ⟨same, _, Q, r, entryQ, entryR, hq, ht, lower⟩
    have eqQ : d.space i = Q := d.spaces.value_eq_of_entry i entryQ
    have eqR : d.rel i = r := d.relations.value_eq_of_entry i entryR
    exact ⟨Subtype.ext same, eqQ.symm ▸ hq, eqQ.symm ▸ ht, eqR.symm ▸ lower⟩
  · rintro ⟨rfl, hq, ht, lower⟩
    exact ⟨rfl, i.property, d.space i, d.rel i, d.space_entry i, d.rel_entry i, hq, ht, lower⟩

end AttachmentBatchInputs
end
end PartitionPilot.Forcing
end OAI
