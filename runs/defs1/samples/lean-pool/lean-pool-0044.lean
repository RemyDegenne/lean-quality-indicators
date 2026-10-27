@[expose] public section

namespace TLA.ProofMode

open TLA LentilLib

/-- Right-fold a list of predicates into a chain of implications to `q`. -/
def repeatedImplies (ps : List (pred σ)) (q : pred σ) : pred σ := ps.foldr tlaImplies q

end TLA.ProofMode
end
