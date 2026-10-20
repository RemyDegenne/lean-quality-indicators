@[expose] public section

namespace RS

section BundleClose

variable (m : ℕ)

/-- The inverse survivor map. -/
noncomputable def bcPhiInv
    (s : Fragment.FoldSurviving
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) (highCross m)) :
    Fin (m + m) :=
  match hs : s.val with
  | Sum.inl a => ⟨a.val, by
      have hnot := (forall_ne_iff_not_mem_flat _ _).mp s.prop
      by_contra hge
      exact hnot ((mem_highCross_flat m s.val).mpr
        (Or.inl ⟨a, hs, by omega⟩))⟩
  | Sum.inr b => ⟨m + b.val, by
      have hnot := (forall_ne_iff_not_mem_flat _ _).mp s.prop
      have hb : b.val < m := by
        by_contra hge
        exact hnot ((mem_highCross_flat m s.val).mpr
          (Or.inr ⟨b, hs, by omega⟩))
      omega⟩

end BundleClose
end RS
end
