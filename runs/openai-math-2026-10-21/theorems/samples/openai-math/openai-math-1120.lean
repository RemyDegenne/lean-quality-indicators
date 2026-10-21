namespace OAI

section

namespace ElementaryPositivity.SlopeArithmetic

variable {I : Type*} [Fintype I]

variable (c η : I → ℝ) (hc : ∀ i,0 < c i)

include hc in

theorem hn_split_triangular {m n : ℕ} (l : Fin m → I → ℕ) (r : Fin n → I → ℕ)
    (q : Fin m → Fin n → I → ℕ) (h : HNSplitMatrix c η l r q)
    (hl : ∀ i,l i≠0) (hr : ∀ j,r j≠0)
    (ho : ∀ j k,j < k → slope c η (r k) < slope c η (r j)) :
    List.Lex (hnKeyLT c η) (List.ofFn l) (List.ofFn r) ∨ List.ofFn l=List.ofFn r := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact Or.inr (by simp)
    | succ n =>
      have hh := h.colSum 0
      simp only [Finset.univ_eq_empty,Finset.sum_empty] at hh
      exact (hr 0 hh.symm).elim
  | succ m ih =>
    cases n with
    | zero =>
      have hh:=h.rowSum 0
      simp only [Finset.univ_eq_empty,Finset.sum_empty] at hh
      exact (hl 0 hh.symm).elim
    | succ n =>
      rcases split_first_row c η hc h (hl 0) (fun j hj=>ho 0 j hj) with hk|⟨he,_,hrow,hcol⟩
      · exact Or.inl (by simpa only [List.ofFn_succ] using List.Lex.rel hk)
      obtain htail|htail:=ih (fun i=>l i.succ) (fun j=>r j.succ) (fun i j=>q i.succ j.succ)
        (split_tail c η h hrow hcol) (fun i=>hl i.succ) (fun j=>hr j.succ)
        (fun j k hjk=>ho j.succ k.succ (Fin.succ_lt_succ_iff.mpr hjk))
      · exact Or.inl (by simpa only [List.ofFn_succ,he] using List.Lex.cons htail)
      · exact Or.inr (by simp only [List.ofFn_succ,he,htail])

end ElementaryPositivity.SlopeArithmetic
end
end OAI
