namespace OAI

namespace CriticalStrip.Diagram

noncomputable section

open Finset

open scoped Classical

namespace Pairing

theorem capRemove_vacant {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b) :
    ¬ (capRemove p a b hab ha hb hn).Occupied a ∧
    ¬ (capRemove p a b hab ha hb hn).Occupied b := by
  have h := adjacent_partners hab (p.partner_adj a ha) (p.partner_adj b hb) hn
  simp only [capRemove,capSplice_occupied,omitTwo_not_occupied_left,
    omitTwo_not_occupied_right,or_false,not_or]
  exact ⟨⟨h.1.symm,h.2.2.1.symm⟩,⟨h.2.1.symm,h.2.2.2.1.symm⟩⟩

end Pairing
end
end CriticalStrip.Diagram
end OAI
