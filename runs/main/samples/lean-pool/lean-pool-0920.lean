@[expose] public section

open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall

namespace GeneralGrushko

universe u

variable {G H : Type u} [Group G] [Group H]

omit [Group G] [Group H] in
@[simp]
theorem rosePosition_last {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) :
    rosePosition w i ⟨(w i).length, by omega⟩ = none := by
  simp [rosePosition]

end GeneralGrushko
end MarshallHall
end
end
