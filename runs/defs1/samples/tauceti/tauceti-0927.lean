public section

namespace TauCeti

namespace BraidGroup

variable {n : ℕ}

/-- The pure braid group: the braids that return every strand to its own position. -/
def pureSubgroup (n : ℕ) : Subgroup (BraidGroup n) := (permHom n).ker

end BraidGroup
end TauCeti
end
