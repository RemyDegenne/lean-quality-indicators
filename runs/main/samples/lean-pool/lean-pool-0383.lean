@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

namespace Sound

variable {Γ : PairGraph} {t : ℕ}

section Nesting

theorem pairSel_bijective {X Y : Finset (GObs Γ t)} (hXY : Disjoint X Y) :
    Function.Bijective (pairSel X Y) := by
  classical
  constructor
  · intro χ χ' h
    funext o
    have hmem : o.1 ∈ X ∨ o.1 ∈ Y := by simpa using o.2
    rcases hmem with hx | hy
    · exact congrFun (congrArg Prod.fst h) ⟨o.1, hx⟩
    · exact congrFun (congrArg Prod.snd h) ⟨o.1, hy⟩
  · rintro ⟨a, b⟩
    refine ⟨fun o => if h : o.1 ∈ X then a ⟨o.1, h⟩ else b ⟨o.1, ?_⟩, ?_⟩
    · have hm : o.1 ∈ X ∨ o.1 ∈ Y := by simpa using o.2
      exact hm.resolve_left h
    · refine Prod.ext ?_ ?_
      · funext o
        exact dite_eq_left o.2
      · funext o
        exact dite_eq_right (Finset.disjoint_right.mp hXY o.2)

end Nesting
end Sound
end TriangleInflation.Graph
end
