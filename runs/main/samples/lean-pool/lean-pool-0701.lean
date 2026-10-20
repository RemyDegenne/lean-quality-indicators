universe u

open Set Pointwise

public noncomputable section

namespace IGame

export Player (left right)

scoped notation:max x:max "ᴸ" => moves left x

scoped notation:max x:max "ᴿ" => moves right x

macro "igame_wf" config:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| all_goals solve_by_elim $config
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop] )

notation:50 x:50 " ⧏ " y:50 => ¬ y ≤ x

theorem zero_lf {x : IGame} : 0 ⧏ x ↔ ∃ y ∈ xᴸ, 0 ≤ y := by
  rw [lf_iff_exists_le]; simp

end IGame
end
