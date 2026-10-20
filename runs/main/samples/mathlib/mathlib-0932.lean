@[expose] public section

namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {u v w : V}

lemma getVert_eq_getD_support {u v : V} (p : G.Walk u v) (n : ℕ) :
    p.getVert n = p.support.getD n v := by
  by_cases h : n ≤ p.length
  · simp [← getVert_eq_support_getElem? p h]
  grind [getVert_of_length_le, length_support]

end Walk
end SimpleGraph
end
