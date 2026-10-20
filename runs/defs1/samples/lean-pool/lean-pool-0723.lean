@[expose] public section

namespace Complexity

attribute [instance] TM.decEq TM.finQ

attribute [instance] NTM.decEq NTM.finQ

namespace NTM

variable {n : ℕ}

/-- NTM accepts `x` within `T` steps: there exists a choice sequence of length `T`
    leading to `qhalt` with output cell 1 = `1`. -/
def AcceptsInTime (tm : NTM n) (x : List Bool) (T : ℕ) : Prop :=
  ∃ choices : Fin T → Bool,
    let c' := tm.trace T choices (tm.initCfg x)
    tm.halted c' ∧ c'.output.cells 1 = Γ.one

end NTM
end Complexity
end
