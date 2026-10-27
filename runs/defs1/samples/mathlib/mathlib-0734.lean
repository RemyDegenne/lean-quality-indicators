@[expose] public section

noncomputable section

open Fintype

variable (M : Type*) [Mul M]

variable [Finite M]

variable {M}

variable (G : Type*) [Group G]

variable {G}

variable [Finite G] (H : Subgroup G)

variable (G)

namespace DihedralGroup

/-- A list of Dihedral groups whose product will have commuting probability `1 / n`. -/
def reciprocalFactors (n : ℕ) : List ℕ :=
  if _ : n = 0 then [0]
  else if _ : n = 1 then []
  else if Even n then
    3 :: reciprocalFactors (n / 2)
  else
    n % 4 * n :: reciprocalFactors (n / 4 + 1)

end DihedralGroup
end
end
