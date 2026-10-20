public section

namespace TauCeti

namespace PDCode

variable {n : ℕ}

section Relabel

variable {m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)

@[simp] theorem relabel_overPair (i : Fin m) :
    (D.relabel half cross).overPair i = D.overPair (cross.symm i) := (rfl)

end Relabel
end PDCode
end TauCeti
end
