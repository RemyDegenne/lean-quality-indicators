@[expose] public section

namespace CircuitComplexity

namespace CNF

/-- The complexity of a CNF formula is its number of clauses. -/
def complexity (φ : CNF N) : Nat := φ.clauses.length

end CNF
end CircuitComplexity
end
