@[expose] public section

universe u

open Set RelSeries

open JordanHolderLattice

namespace CompositionSeries

variable {X : Type u} [Lattice X] [JordanHolderLattice X]

theorem exists_last_eq_snoc_equivalent (s : CompositionSeries X) (x : X) (hm : IsMaximal x s.last)
    (hb : s.head ≤ x) :
    ∃ t : CompositionSeries X,
      t.head = s.head ∧ t.length + 1 = s.length ∧
      ∃ htx : t.last = x,
        Equivalent s (snoc t s.last (show IsMaximal t.last _ from htx.symm ▸ hm)) := by
  induction hn : s.length generalizing s x with
  | zero =>
    exact (ne_of_gt (lt_of_le_of_lt hb (lt_of_isMaximal hm))
      (subsingleton_of_length_eq_zero hn s.last_mem s.head_mem)).elim
  | succ n ih =>
    have h0s : 0 < s.length := hn.symm ▸ Nat.succ_pos _
    by_cases hetx : s.eraseLast.last = x
    · use s.eraseLast
      simp [← hetx, hn, Equivalent.refl]
    · have imxs : IsMaximal (x ⊓ s.eraseLast.last) s.eraseLast.last :=
        isMaximal_of_eq_inf x s.last rfl (Ne.symm hetx) hm (isMaximal_eraseLast_last h0s)
      have := ih _ _ imxs (le_inf (by simpa) (le_last_of_mem s.eraseLast.head_mem)) (by simp [hn])
      rcases this with ⟨t, htb, htl, htt, hteqv⟩
      have hmtx : IsMaximal t.last x :=
        isMaximal_of_eq_inf s.eraseLast.last s.last (by rw [inf_comm, htt]) hetx
          (isMaximal_eraseLast_last h0s) hm
      use snoc t x hmtx
      refine ⟨by simp [htb], by simp [htl], by simp, ?_⟩
      have : s.Equivalent ((snoc t s.eraseLast.last <| show IsMaximal t.last _ from
        htt.symm ▸ imxs).snoc s.last
          (by simpa using isMaximal_eraseLast_last h0s)) := by
        conv_lhs => rw [eq_snoc_eraseLast h0s]
        exact Equivalent.snoc hteqv (by simpa using iso_refl)
      refine this.trans <| Equivalent.snoc_snoc_swap
        (iso_symm
            (second_iso_of_eq hm
              (sup_eq_of_isMaximal hm (isMaximal_eraseLast_last h0s) (Ne.symm hetx)) htt.symm))
        (second_iso_of_eq (isMaximal_eraseLast_last h0s)
            (sup_eq_of_isMaximal (isMaximal_eraseLast_last h0s) hm hetx) (by rw [inf_comm, htt]))

end CompositionSeries
end
