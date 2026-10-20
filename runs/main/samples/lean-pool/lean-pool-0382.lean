@[expose] public section

open Equiv Equiv.Perm Fintype

theorem no_crossing_imp_IsNoncrossing {n : ℕ} (p : Pairing n)
    (h : ¬p.HasCrossing) : p.IsNoncrossing := by
  induction n with
  | zero => exact trivial
  | succ n ih =>
    obtain ⟨i, hadj⟩ := no_crossing_has_adjacent p h
    refine ⟨i, hadj, ih (p.deleteAdjacent i hadj) ?_⟩
    intro hcross
    exact h (deleteAdjacent_crossing_lifts p i hadj hcross)

end
