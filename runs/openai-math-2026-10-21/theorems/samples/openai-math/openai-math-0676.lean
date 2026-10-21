namespace OAI

section

namespace PlanarL1.Columns.Model

namespace Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

lemma NearColumns.union {x : M.Point I root} {A : ℝ} {S T : Set (Fin n)}
    (hS : x.NearColumns J A S) (hT : x.NearColumns J A T) :
    x.NearColumns J A (S ∪ T) := fun v hv => hv.elim (hS v) (hT v)

end Point
end PlanarL1.Columns.Model
end
end OAI
