set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

noncomputable section

namespace CorestrictionTransversal

variable {H : Subgroup G} (T : H.RightTransversal)

/-- Matching representatives of two right transversals gives an equivalence. -/
@[expose]
def changeRepEquiv (S : H.RightTransversal) :
    ↥(T : Set G) ≃ ↥(S : Set G) where
  toFun := changeRep T S
  invFun := changeRep S T
  left_inv t := by
    change (T.2.equiv (changeRep T S t : G)).2 = t
    calc
      _ = (T.2.equiv (t : G)).2 :=
        T.2.equiv_snd_eq_iff_rightCosetEquivalence.2 (changeRep_rightCoset T S t)
      _ = t := T.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem t.2
  right_inv s := by
    change (S.2.equiv (changeRep S T s : G)).2 = s
    calc
      _ = (S.2.equiv (s : G)).2 :=
        S.2.equiv_snd_eq_iff_rightCosetEquivalence.2 (changeRep_rightCoset S T s)
      _ = s := S.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem s.2

end CorestrictionTransversal
end
end ContinuousCohomology
end
