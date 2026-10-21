namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueSize

open WordOperations WordList RationalHeight

variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}

omit [LinearOrder L] in
lemma atom_bound (el : L→List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→L) (q : R→Fin n→ℚ) (a : BlueDP.Atom L R (Fin n)) (h : a.2.1∈B ∧ label a.2.1=a.1 ∧ a.2.2∈F) :
    let N:=(BinaryBlueItem.records el er B label q).length
    (BinaryBlueItem.atomEnc el er a).length≤5*N+2 ∧ Height (q a.2.1 a.2.2) N := by
  dsimp only
  have hr : (BinaryBlueItem.record el er label q a.2.1).length≤(BinaryBlueItem.records el er B label q).length :=
    length_member_le_encode (List.mem_map.mpr ⟨a.2.1,(Finset.mem_sort (·≤·)).mpr h.1,rfl⟩)
  have hq := RationalArray.input_height (List.ofFn (q a.2.1)) (q a.2.1 a.2.2) (List.mem_ofFn.mpr ⟨a.2.2,rfl⟩)
  have hn : n≤(RationalArray.encode (List.ofFn (q a.2.1))).length := by
    simpa only [RationalArray.encode,List.length_map,List.length_ofFn] using
      length_le_encode ((List.ofFn (q a.2.1)).map BinaryRational.encode)
  have hb : a.2.2.val.bits.length≤n := (by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self : a.2.2.val.bits.length≤a.2.2.val).trans (Nat.le_of_lt a.2.2.isLt)
  simp only [BinaryBlueItem.record,pairBits_length] at hr
  refine ⟨?_,hq.mono (by omega)⟩
  simp only [BinaryBlueItem.atomEnc,pairBits_length]
  rw [←h.2.1]
  omega

end MetricKMedianRecovery.BitMachine.BinaryBlueSize
end OAI
