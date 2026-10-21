namespace OAI

namespace IndependentSetsCut.CounterMachine

section

open scoped BigOperators

variable {R : Type} [DecidableEq R]

omit [DecidableEq R] in
@[ext] theorem Data.ext {d e : Data R} (hr : d.reg = e.reg)
    (hi : d.input = e.input) (hb : d.backup = e.backup) (ho : d.output = e.output) : d = e := by
  cases d; cases e; simp_all

end
end IndependentSetsCut.CounterMachine
end OAI
