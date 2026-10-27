public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.RepresentationTheory

variable {K : Type*} [Field K]

theorem not_forall_scalar_of_perfect {G : Subgroup (GL (Fin 3) K)} (A : Subgroup G)
    [Group.IsPerfect A] (hA : A ≠ ⊥) :
    ¬ ∀ x ∈ A.map G.subtype, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  intro h
  apply hA
  apply ComponentClassification.Quasisimple.perfect_le_center_eq_bot A
  intro a ha
  obtain ⟨c, hc⟩ := h _ (Subgroup.mem_map_of_mem _ ha)
  exact mem_center_of_scalar hc

end CFSG.RankThree.SubgroupLists
end
