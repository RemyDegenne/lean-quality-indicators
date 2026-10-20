public section

namespace TauCeti

open _root_.Quiver

universe u

namespace DoubledQuiver

variable {V : Type u} (G : SimpleGraph V)

namespace OrientedQuiver

variable (o : Orientation G)

theorem exists_eq_arrow {i j : V} (e : vertex G o i ⟶ vertex G o j) :
    ∃ (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o), e = arrow G o h ho :=
  ⟨(homEquiv G o i j e).1, (homEquiv G o i j e).2, Subsingleton.elim _ _⟩

end OrientedQuiver
end DoubledQuiver
end TauCeti
end
