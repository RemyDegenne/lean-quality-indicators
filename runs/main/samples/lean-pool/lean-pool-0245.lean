namespace MisereGames

public section

namespace Form.Misere.Outcome

open Form

universe u

variable {G : Type (u + 1)} [Form G]

@[inherit_doc MisereEQ]
syntax (name := misereEQ) term:51 " =m " term:max term:51 : term

macro_rules (kind := misereEQ)
  | `($x =m $u $y) => `(MisereEQ $u $x $y)

open Lean PrettyPrinter Delaborator SubExpr

theorem MisereEQ.trans {A : G → Prop} {g h k : G} (h1 : g =m A h) (h2 : h =m A k) :
    g =m A k := by
  unfold MisereEQ at *
  simp_all

end Form.Misere.Outcome
end
end MisereGames
