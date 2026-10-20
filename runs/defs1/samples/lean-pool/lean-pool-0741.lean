@[expose] public section

namespace CircuitComplexity

namespace ShannonUpper

/-- Cumulative gate offset after Section F of the construction. -/
def oF (kk qq : Nat) : Nat := oE kk qq + 2 ^ qq

end ShannonUpper
end CircuitComplexity
end
