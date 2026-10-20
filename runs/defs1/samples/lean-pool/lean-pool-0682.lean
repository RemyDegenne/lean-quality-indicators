@[expose] public section

namespace BKAR

namespace Forest

variable {V} [Fintype V] [DecidableEq V]

/--
Certificate that `F'` is obtained from `F` by adding one edge and that the canonical
paths behave as expected under this extension.
-/
structure EdgeExtension (F F' : Forest V) (e₀ : Edge V) where
  new_not_mem : e₀ ∉ F.edges
  edges_eq : F'.edges = insert e₀ F.edges
  old_component :
    ∀ {i j : V}, F.inSameComponent i j → F'.inSameComponent i j
  old_path :
    ∀ {i j : V} (h : F.inSameComponent i j),
      F'.pathInF i j (old_component h) = F.pathInF i j h
  new_path_uses :
    ∀ {i j : V} (_ : ¬ F.inSameComponent i j)
      (hF' : F'.inSameComponent i j), e₀ ∈ F'.pathInF i j hF'

end Forest
end BKAR
end
