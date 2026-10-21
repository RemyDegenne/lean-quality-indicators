namespace OAI

namespace DFVSGames.Explicit

open DFVSGames.Foundations.Games

open scoped BigOperators

namespace BipartiteGame

variable {L R E A : Type*}

@[simp] theorem product_permutation (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (a : Fin t → A) (i : Fin t) :
    (G.product t).permutation e a i = G.permutation (e i) (a i) := rfl

end BipartiteGame
end DFVSGames.Explicit
end OAI
