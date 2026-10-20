@[expose] public section

namespace RS

variable {α : Type}

namespace EdgeSubset

variable {W : Fragment α} {F : EdgeSubset W}

namespace RelTransitionSystem

theorem repair_repair {κ : F.RelTransitionSystem}
    {a b c d : W.Flag} {v : W.Vertex} (h : RepairSquare κ a b c d v)
    (h₂ : RepairSquare (κ.repair a b c d v h) a c b d v) :
    ((κ.repair a b c d v h).repair a c b d v h₂).MatchEq κ := by
  intro f hf
  by_cases h1 : f = a
  · subst h1
    rw [repair_match_a h₂, h.hab]
  by_cases h2 : f = b
  · subst h2
    rw [repair_match_c h₂, h.hmb]
  by_cases h3 : f = c
  · subst h3
    rw [repair_match_b h₂, h.hcd]
  by_cases h4 : f = d
  · subst h4
    rw [repair_match_d h₂, h.hmd]
  · rw [repair_match_of_ne h₂ h1 h3 h2 h4,
      repair_match_of_ne h h1 h2 h3 h4]

end RelTransitionSystem
end EdgeSubset
end RS
end
