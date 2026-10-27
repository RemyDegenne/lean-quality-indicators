@[expose] public section

namespace CircuitComplexity

namespace CNF

/-- The complexity of a CNF formula is its number of clauses. -/
def complexity (φ : CNF N) : Nat := φ.clauses.length + 1

end CNF
end CircuitComplexity
end
