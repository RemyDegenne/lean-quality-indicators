@[expose] public section

namespace LO

namespace FirstOrder

namespace Language

notation "ℒₒᵣ" => oRing

/-- Imported declaration from the Incompleteness formalization. -/
protected class Pow (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  pow : L.Func 2

end Language
end FirstOrder
end LO
end
