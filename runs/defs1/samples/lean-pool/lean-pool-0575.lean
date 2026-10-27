@[expose] public section

namespace Circuit

/-- Logic gate. -/
class Gate (V : outParam Type*) [Preorder V] (G : Type*) where
  /-- The number of input wires of a gate. -/
  inputs : G → ℕ
  /-- The number of output wires of a gate. -/
  outputs : G → ℕ
  /-- The wire-function computed by a gate. -/
  gate (g : G) : Wires V (inputs g) → Wires V (outputs g)
  /-- The wire-function of a gate is monotone in the information order. -/
  gate_monotone (g : G) : Monotone (gate g)

end Circuit
end
