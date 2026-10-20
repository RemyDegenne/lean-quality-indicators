@[expose] public section

namespace GaleStewartGame

open Stream'.Discrete Descriptive Tree

variable {A : Type*} {p : Player}

namespace Game

@[simp] lemma residual_nil (G : Game A) : G.residual [] = G := rfl

end Game
end GaleStewartGame
end
