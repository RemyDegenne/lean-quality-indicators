@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace CommSq

variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}

variable (sq : CommSq f i p g)

/-- The assertion that a square has a `LiftStruct`. -/
@[to_dual self]
class HasLift : Prop where
  /-- Square has a `LiftStruct`. -/
  exists_lift : Nonempty sq.LiftStruct

end CommSq
end CategoryTheory
end
