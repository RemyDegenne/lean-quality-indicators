@[expose] public section

namespace CircuitComplexity

namespace ShannonUpper

/-- Number of data variables: `N - addrBits N`. -/
def dataBits (N : Nat) : Nat := N - addrBits N

end ShannonUpper
end CircuitComplexity
end
