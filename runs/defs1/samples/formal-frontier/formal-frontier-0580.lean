@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

/-- The canonical map to the maximal pro-`p` quotient, as a function. -/
def etaFn (x : G) : product p G :=
  ⟨fun _ ↦ QuotientGroup.mk x, fun _ _ _ ↦ rfl⟩

end MaximalProPQuotient
end ProfiniteGrp
end
