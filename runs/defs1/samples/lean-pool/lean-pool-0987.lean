@[expose] public section

namespace LO

namespace Modal

open Formula.Kripke

namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev TransitiveIrreflexiveFiniteFrameClass : FiniteFrameClass :=
  { F | IsTrans F.World F.Rel ∧ Std.Irrefl F.Rel }

end Kripke
end Modal
end LO
end
