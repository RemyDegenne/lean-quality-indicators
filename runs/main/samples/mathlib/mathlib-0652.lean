@[expose] public section

open Filter Set Int

open Function hiding Commute

open scoped Topology

namespace CircleDeg1Lift

variable (f g : CircleDeg1Lift)

@[simp]
theorem translate_pow (x : ℝ) (n : ℕ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) :=
  translate_zpow x n

end CircleDeg1Lift
end
