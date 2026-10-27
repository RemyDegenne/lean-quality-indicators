@[expose] public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

/-- The elementary unit at a strictly upper-triangular position, in the unitriangular subgroup. -/
def elementary (i j : Fin n) (hij : i < j) (a : R) :
    Matrix.UnitriangularGroup (Fin n) R := by
  refine ⟨Matrix.GeneralLinearGroup.elementaryUnit i j (ne_of_lt hij) a, ?_⟩
  refine ⟨?_, ?_⟩
  · change (1 + Matrix.single i j a : Matrix (Fin n) (Fin n) R).IsUpperTriangular
    exact Matrix.blockTriangular_one.add (Matrix.blockTriangular_single hij.le a)
  · intro k
    change (1 + Matrix.single i j a : Matrix (Fin n) (Fin n) R) k k = 1
    have h : ¬ (i = k ∧ j = k) := fun h => (ne_of_lt hij) (h.1.trans h.2.symm)
    simp [Matrix.add_apply, h]

end Matrix.UnitriangularGroup
end
