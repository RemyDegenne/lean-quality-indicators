@[expose] public section

namespace Domain.Neighborhood.Exercise516

open Domain.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

variable {β : Type*}

/-- The value of `tail` on a total element `σ`: `tail(Λ) = ⊥`, `tail(bσ') = σ'`. -/
def tailSing : Str → C.Element
  | [] => strBot []
  | _ :: σ' => strElem σ'

end Domain.Neighborhood.Exercise516
end
