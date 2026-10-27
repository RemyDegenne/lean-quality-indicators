namespace MisereGames

public section

universe u

/--
Type class for the `ofSets` operation. Used to implement the `!{st}` and `!{s |
t}` syntax.
-/
class OfSets (α : Type (u + 1)) (Valid : outParam ((Player → Set α) → Prop)) where
  /--
  Construct a combinatorial game from its Left and Right option sets.
  -/
  ofSets (st : Player → Set α) (h : Valid st) [Small.{u} (st .left)] [Small.{u} (st .right)] : α

end
end MisereGames
