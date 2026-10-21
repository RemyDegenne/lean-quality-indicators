namespace OAI

section

namespace Erdos3

theorem fastTerminalParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fastTerminalParameter p ∧ (3 * p + 2) ^ 294 ≤ fastTerminalParameter p ∧
      (p + 2) ^ 7 ≤ fastTerminalParameter p :=
  doublePowerParameter_controls 294 7 hp

end Erdos3
end
end OAI
