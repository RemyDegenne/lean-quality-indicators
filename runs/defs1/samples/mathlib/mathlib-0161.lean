public section

/-- A notation class for the *negative part* function (multiplicative version): `a⁻ᵐ`. -/
@[to_additive]
class LeOnePart (α : Type*) where
  /-- The *negative part* of an element `a`. -/
  leOnePart : α → α

end
