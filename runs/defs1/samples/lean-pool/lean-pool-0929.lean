@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace GerverSofa

open RatInterval

/-- A rational interval list encloses a finite real vector coordinatewise. -/
def EnclosesVec {n : Nat} (box : List RatInterval) (x : Vec n) : Prop :=
  box.length = n ∧
    ∀ i : Fin n, Contains (box.getD i.1 (point 0)) (x i)

end GerverSofa
end
end
end
end
end
end
end
end
