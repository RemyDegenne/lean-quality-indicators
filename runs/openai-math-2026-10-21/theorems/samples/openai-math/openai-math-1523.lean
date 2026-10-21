namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

lemma latticeBall_finite {d : ℕ} (x : Lattice d) (n : ℕ) :
    (LatticeBall x n).Finite := by
  have he : LatticeBall x n = Set.Icc (x - fun _ => (n : ℤ)) (x + fun _ => (n : ℤ)) := by
    ext y
    simp only [LatticeBall, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def,
      Pi.sub_apply, Pi.add_apply]
    constructor
    · intro h
      exact ⟨fun i => by have := (abs_le.mp (h i)).1; omega,
        fun i => by have := (abs_le.mp (h i)).2; omega⟩
    · rintro ⟨h, h'⟩ i
      exact abs_le.mpr ⟨by have := h i; omega, by have := h' i; omega⟩
  rw [he]
  exact Set.finite_Icc _ _

end DirectionalTransience
end
end
end OAI
