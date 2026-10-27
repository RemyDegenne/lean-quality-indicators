namespace MisereGames

open GameForm

open Form

public section

/--
A `Shove` position is a strip board (a function from positions to pieces with
finite support).
-/
structure Shove where
  /-- The underlying strip board. -/
  toBoard : Strip.Board

end
end MisereGames
