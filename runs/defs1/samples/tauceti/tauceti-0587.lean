public section

namespace TauCeti

namespace ClassData

universe u

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

variable (d : ClassData G)

/-- The executable Boolean checker for an integer central-character table, ordinary table, and
their character degrees. -/
def integerCharacterTableChecker
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (degree : Fin d.numClasses → ℕ) : Bool :=
  d.exactCharacterTableChecker (fun x => x) omega table degree

end ClassData
end TauCeti
end
