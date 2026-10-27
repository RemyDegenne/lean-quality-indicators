@[expose] public section

namespace PDL

open Typ

open QuasiTab

namespace QuasiTab

/-- Def 9.11: the companion `c(x)` of a repeat leaf `x`, that is, the node `z <_Q x` of
type 1 with the same label as `x`. Because repeats are identified at the first opportunity
there is at most one such node in a quasi-tableau; here we simply take the one closest to
the root. -/
def companionOpt (q : QuasiTab) (x : List Nat) : Option (List Nat) :=
  x.inits.dropLast.find? (fun z => decide (q.labelAt z = q.labelAt x ∧ q.typAt z = some .one))

end QuasiTab
end PDL
end
