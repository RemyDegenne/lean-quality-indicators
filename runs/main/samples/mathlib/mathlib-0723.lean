@[expose] public section

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section OrderedWeight

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

lemma weightOfEPs_pos {w : V → V → R}
    (hw : ∀ i j : V, 0 < w i j) {i j : V} (p : Path i j) :
    0 < weightOfEPs w p := by
  apply weight_pos
  intro i j e
  exact hw _ _

end OrderedWeight
end Quiver.Path
end
