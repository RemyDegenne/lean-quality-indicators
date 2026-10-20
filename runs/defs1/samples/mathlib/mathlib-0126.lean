@[expose] public section

/-- A type synonym for non-unital rings where an alternative monoid structure is introduced.
If `R` is a non-unital semiring, then `PreQuasiregular R` is equipped with the monoid structure
with binary operation `fun x y ↦ y + x + x * y` and identity `0`. Elements of `R` which are
invertible in this monoid satisfy the predicate `IsQuasiregular`. -/
structure PreQuasiregular (R : Type*) where
  /-- The value wrapped into a term of `PreQuasiregular`. -/
  val : R

end
