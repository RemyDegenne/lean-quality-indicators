namespace OAI

section

namespace MeanPayoff

open scoped Classical

theorem tightSub_forces_update (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (y : Vec (Fin G.n)) (r : BoxVector I) (hr : tightSub G I y ≤ r.val) :
    ∃ i, (I.delta : ℤ) ≤ r.val i - I.a i := by
  obtain ⟨i, hi⟩ := deviation_attained G y I.a
  have hh := (le_max_left (y i - deviation G y I.a + I.delta) (I.a i)).trans (hr i)
  exact ⟨i, by omega⟩

end MeanPayoff
end
end OAI
