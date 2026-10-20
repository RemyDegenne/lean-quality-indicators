namespace MisereGames

public section

namespace Form.Misere.Outcome

open Form

universe u

variable {G : Type (u + 1)} [Form G]

@[simp]
theorem winsGoingFirst_of_isEndLike {g : G} {p : Player} (h1 : IsEndLike p g) :
    WinsGoingFirst p g :=
  (winsGoingFirst_iff g p).mpr (Or.inl h1)

end Form.Misere.Outcome
end
end MisereGames
