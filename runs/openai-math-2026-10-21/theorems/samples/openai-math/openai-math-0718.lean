namespace OAI

namespace BinPackingGames.Reduction.CloneGap

variable {α : Type _} {β : Type _}

theorem length_cart (xs : List α) (ys : List β) :
    (cart xs ys).length = xs.length * ys.length := by
  have := count_cart xs ys (fun _ => true) (fun _ => true)
  simpa using this

end BinPackingGames.Reduction.CloneGap
end OAI
